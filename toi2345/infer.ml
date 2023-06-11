type constraint_t = Type.t * Type.t

module SchemaEnv = Schema.SchemaEnv

exception RecursiveOccurenceError of Type.typevar_t * Type.t
exception BadConstraintError of Type.t * Type.t

module UnionFind = struct
  let father : (Type.t, Type.t) Hashtbl.t = Hashtbl.create 0
  let rk : (Type.t, int) Hashtbl.t = Hashtbl.create 0
  let representative : (Type.t, Type.t) Hashtbl.t = Hashtbl.create 0

  let rank x =
    match Hashtbl.find_opt rk x with
    | Some r -> r
    | None ->
        Hashtbl.add rk x 0;
        0

  let rec find x =
    match Hashtbl.find_opt father x with
    | Some x' ->
        if x = x' then x
        else
          let f' = find x' in
          Hashtbl.replace father x f';
          f'
    | None ->
        Hashtbl.add father x x;
        if not (Type.is_typevar x) then Hashtbl.add representative x x;
        x

  let represent x =
    let f = find x in
    match Hashtbl.find_opt representative f with Some x' -> x' | None -> f

  let rec apply = function
    | `Int -> `Int
    | `Bool -> `Bool
    | `Unit -> `Unit
    | `Func (t1, t2) ->
        if t1 != t2 then `Func (apply t1, apply t2)
        else
          let t1' = apply t1 in
          `Func (t1', t1')
    | `Tuple ts ->
        List.fold_left
          (fun acc t ->
            match List.assq_opt t acc with
            | Some t' -> (t, t') :: acc
            | None -> (t, apply t) :: acc)
          [] ts
        |> List.split |> snd |> List.rev
        |> fun ts' -> `Tuple ts'
    | `TypeVar _ as beta ->
        let t = represent beta in
        if beta <> t then
          if beta |> Type.occurs_in t then
            raise (RecursiveOccurenceError (beta, t))
          else apply t
        else t

  let apply_schema (s : Schema.schema) =
    let rec apply' = function
      | `Int -> `Int
      | `Bool -> `Bool
      | `Unit -> `Unit
      | `Func (t1, t2) ->
          if t1 != t2 then `Func (apply' t1, apply' t2)
          else
            let t1' = apply' t1 in
            `Func (t1', t1')
      | `Tuple ts ->
          List.fold_left
            (fun acc t ->
              match List.assq_opt t acc with
              | Some t' -> (t, t') :: acc
              | None -> (t, apply t) :: acc)
            [] ts
          |> List.split |> snd |> List.rev
          |> fun ts' -> `Tuple ts'
      | `TypeVar _ as beta ->
          if Type.TypeVarSet.mem beta s.fv then
            let t = find beta in
            if beta |> Type.occurs_in t && beta <> t then
              raise (RecursiveOccurenceError (beta, t))
            else t
          else beta
    in
    let body' = apply' s.body in
    assert (body' = apply s.body);
    Schema.schema s.polys body'
  (* TODO fix this inefficiency *)

  let merge x1 x2 =
    let f1, f2 = (find x1, find x2) in
    if f1 <> f2 then (
      if not (Type.is_typevar f1) then Hashtbl.replace representative f2 f1;
      if not (Type.is_typevar f2) then Hashtbl.replace representative f1 f2;
      let c = rank f1 - rank f2 in
      if c > 0 then Hashtbl.replace father f2 f1
      else Hashtbl.replace father f1 f2;
      if c = 0 then
        let rk_f2 = Hashtbl.find rk f2 in
        Hashtbl.replace rk f2 (rk_f2 + 1))

  let string_of_father () =
    let groups = Hashtbl.create 0 in
    father |> Hashtbl.to_seq
    |> Seq.iter (fun (alpha, _) -> Hashtbl.add groups (find alpha) alpha);
    groups |> Hashtbl.to_seq
    |> Seq.group (fun (alpha, _) (beta, _) -> alpha = beta)
    |> Seq.map (fun g ->
           g
           |> Seq.map (fun (_, t) -> Type.string_of t)
           |> List.of_seq |> String.concat ", " |> Printf.sprintf "[%s]")
    |> List.of_seq |> String.concat "; " |> Printf.sprintf "[%s]"
  (* |> Seq.map (fun (s1, s2) -> Printf.sprintf "%s : %s" s1 s2)
     |> List.of_seq |> String.concat "; " |> Printf.sprintf "[%s]" *)
end

(* module Substitutes = Map.Make (struct
     type t = Type.typevar_t

     let compare (`TypeVar i) (`TypeVar j) = i - j
   end) *)

(* let simplify_subst (substs : Type.t Substitutes.t) : [`Func of Type.t * Type.t | `Int | `Bool | `Unit] Substitutes.t=
   let substs' =
     substs |> Substitutes.to_seq
     |> Seq.filter (fun (alpha, t) ->
            match t with
            | `TypeVar _ as beta -> Substs.UFSet.f alpha = Substs.UFSet.f beta
            | _ -> true)
   in
   assert (
     substs'
     |> Seq.for_all (fun (_, t) ->
            match t with #Type.typevar_t -> false | _ -> true));

   substs'
   |> Seq.map (fun (alpha, t) -> (Substs.UFSet.f alpha, Substs.UFSet.normalize t))
   |> Substitutes.of_seq *)

(* let infer_ii_i (t1 : Type.t) (c1 : constraint_t list) (t2 : Type.t)
       (c2 : constraint_t list) =
     (`Int, ((t2, `Int) :: (t1, `Int) :: c2) @ c1)

   let infer_ii_b (t1 : Type.t) (c1 : constraint_t list) (t2 : Type.t)
       (c2 : constraint_t list) =
     (`Bool, ((t2, `Int) :: (t1, `Int) :: c2) @ c1)

   let infer_bb_b (t1 : Type.t) (c1 : constraint_t list) (t2 : Type.t)
       (c2 : constraint_t list) =
     (`Bool, ((t2, `Bool) :: (t1, `Bool) :: c2) @ c1)

   let infer_eq (t1 : Type.t) (c1 : constraint_t list) (t2 : Type.t)
       (c2 : constraint_t list) =
     (`Bool, ((t1, t2) :: c2) @ c1)

   let binaryOpEnv =
     ref
       [
         ("+", infer_ii_i);
         ("-", infer_ii_i);
         ("*", infer_ii_i);
         ("/", infer_ii_i);
         ("mod", infer_ii_i);
         ("||", infer_bb_b);
         ("&&", infer_bb_b);
         ("=", infer_eq);
         ("<", infer_ii_b);
         ("<=", infer_ii_b);
         (">", infer_ii_b);
         (">=", infer_ii_b);
       ]

   let register_binary_op (op : string) f =
     binaryOpEnv := !binaryOpEnv |> Env.extend op f

   let infer_binaryOp (_ : SchemaEnv.t) (op : string) = Env.lookup op !binaryOpEnv *)
let instantiate (s : Schema.schema) : Type.t =
  let table = Hashtbl.create (Type.TypeVarSet.cardinal s.polys) in
  Type.TypeVarSet.iter
    (fun alpha -> Hashtbl.add table alpha (Type.new_typevar () :> Type.t))
    s.polys;
  let rec instantiate' = function
    | `Int -> `Int
    | `Bool -> `Bool
    | `Unit -> `Unit
    | `Func (t1, t2) as f ->
        if Type.TypeVarSet.disjoint (Type.fv f) s.polys then f
        else if t1 != t2 then `Func (instantiate' t1, instantiate' t2)
        else
          let t1' = instantiate' t1 in
          `Func (t1', t1')
    | `Tuple ts as tuple ->
        assert (List.length ts = 2);
        if Type.TypeVarSet.disjoint (Type.fv tuple) s.polys then tuple
        else
          List.fold_left
            (fun acc t ->
              match List.assq_opt t acc with
              | Some t' -> (t, t') :: acc
              | None -> (t, instantiate' t) :: acc)
            [] ts
          |> List.split |> snd |> List.rev
          |> fun ts' -> `Tuple ts'
    | `TypeVar _ as alpha ->
        if Type.TypeVarSet.mem alpha s.polys then Hashtbl.find table alpha
        else alpha
  in
  instantiate' s.body

let rec generalize (c : constraint_t list) =
  unify c;
  fun (env : SchemaEnv.t) ->
    let env' = SchemaEnv.map UnionFind.apply_schema env in
    fun (t : Type.t) ->
      let typ = UnionFind.apply t in
      assert (typ = UnionFind.apply typ);
      (* assert (Type.fv typ |> Type.TypeVarSet.is_empty |> not); *)
      (* assert (env'.fv |> Type.TypeVarSet.is_empty); *)
      let polys = Type.TypeVarSet.diff (Type.fv typ) env'.fv in
      let s = Schema.schema polys typ in
      if Debug.debug_flag then (
        Printf.printf "father=%s\n" (UnionFind.string_of_father ());
        Printf.printf "t = %s\n" (Type.string_of t);
        Printf.printf "generalize %s to %s\n" (Type.string_of typ)
          (Schema.string_of_schema s));
      (* assert (Type.TypeVarSet.is_empty polys |> not); *)
      s

and infer_expr (schema_env : SchemaEnv.t) e : Type.t * constraint_t list =
  match e with
  | `EConstInt _ -> (`Int, [])
  | `EConstBool _ -> (`Bool, [])
  | `EConstUnit -> (`Unit, [])
  | `EVar x -> (
      try
        let s = schema_env |> SchemaEnv.lookup x in
        let typ = s |> instantiate in
        if Debug.debug_flag then
          Printf.printf "instantiate %s : %s to  %s\n" x
            (Schema.string_of_schema s)
            (Type.string_of typ);
        (typ, [])
      with Not_found -> raise (Transform.UnboundVariable x))
  | `EIf (e1, e2, e3) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let t3, c3 = infer_expr schema_env e3 in
      (t2, ((t2, t3) :: c3) @ c2 @ ((t1, `Bool) :: c1))
  (* | `EBinaryOp (op, e1, e2) ->
         let t1, c1 = infer_expr schema_env e1 in
         (* assert (s1.polys = []); *)
         let t2, c2 = infer_expr schema_env e2 in
         (* assert (s2.polys = []); *)
         let t, c = infer_binaryOp schema_env op t1 c1 t2 c2 in
         (t, c)
     | `EUnaryOp (_, e) ->
         let t, c = infer_expr schema_env e in
         (`Int, (t, `Int) :: c) *)
  | `EFun (_, var, body) ->
      let alpha = Type.new_typevar () in
      let s_alpha = Schema.schema Type.TypeVarSet.empty (alpha :> Type.t) in
      let env' = schema_env |> SchemaEnv.extend var s_alpha in
      let t, c = infer_expr env' body in
      (Type.func ((alpha :> Type.t), t), c)
  (* | `EDFun (_, var, body) ->
      let free_vars = Expr.free_vars e |> Expr.StringSet.elements in
      let alphas =
        Type.new_typevar () :: List.map (fun _ -> Type.new_typevar ()) free_vars
      in
      let s_alphas =
        List.map (Schema.schema Type.TypeVarSet.empty) (alphas :> Type.t list)
      in
      let env' = schema_env |> SchemaEnv.extends (var :: free_vars) s_alphas in
      let t, c = infer_expr env' body in
      (Type.func ((List.hd alphas :> Type.t), t), c) *)
  | `ECall (e1, e2) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let alpha = Type.new_typevar () in
      let alpha' :> Type.t = alpha in
      (alpha', ((t1, Type.func (t2, alpha')) :: c2) @ c1)
  | `ETuple es ->
      let ts, cs = List.map (infer_expr schema_env) es |> List.split in
      let ts' = ts and cs' = cs |> List.rev |> List.concat in
      (`Tuple ts', cs')
  | `ELet ((names, e1s), e2) ->
      let ss =
        List.map
          (fun e ->
            let t, c = infer_expr schema_env e in
            let s = generalize c schema_env t in
            s)
          e1s
      in
      let schema_env' = schema_env |> SchemaEnv.extends names ss in
      let t, c = infer_expr schema_env' e2 in
      (t, c)
  (* let s1s, c1s = List.map (fun e -> let s, c, _=infer_expr schema_env env_monos e in s, c) e1s |> List.split in
     let c1s' = List.rev c1s |> List.concat in
     let schema_env' = schema_env |> Env.extends names s1s in
     let s2, c2 = infer_expr schema_env' e2 in
     (*assert (s2.polys=[]);*)
     (s2, c2 @ c1s') *)
  (* | `ELetRec (f, `EFun (_, x, e1), e2) -> *)
  | `ELetRec ((names, funcs), e2) ->
      let typevars =
        List.init (List.length names) (fun _ ->
            let alpha = Type.new_typevar () in
            (* let beta = Type.new_typevar () in *)
            alpha)
      in
      let schemas : Schema.schema list =
        List.map
          (fun alpha ->
            let polys = Type.TypeVarSet.singleton alpha
            and body :> Type.t = alpha in
            Schema.schema polys body)
          typevars
      in
      let schema_env' = schema_env |> SchemaEnv.extends names schemas in
      let t1s, c1s = List.map (infer_expr schema_env') funcs |> List.split in
      let c1s' = List.rev c1s |> List.concat in
      let g = generalize c1s' schema_env' in
      let s1s = t1s |> List.map (fun t -> g t) in
      (*assert (s1.polys=[]);*)
      let s2, c2 = infer_expr (schema_env |> SchemaEnv.extends names s1s) e2 in
      (*assert (s2.polys=[]);*)
      (s2, c2 @ c1s')
(* let alpha = Type.new_typevar () in
   let beta = Type.new_typevar () in
   let s_x : Schema.schema_t =
     { polys = []; monos = [ alpha ]; body = (alpha :> Type.t) }
   and s_f : Schema.schema_t =
     {
       polys = [ alpha ];
       monos = [ beta ];
       body = `Func ((alpha :> Type.t), (beta :> Type.t));
     }
   in
   let schema_env' = schema_env |> Env.extend x s_x |> Env.extend f s_f in
   let s1, c1 = infer_expr schema_env' e1 in
   (*assert (s1.polys=[]);*)
   let s2, c2 = infer_expr (schema_env |> Env.extend f s_f) e2 in
   (*assert (s2.polys=[]);*)
   (s2, ((s1.body, (beta :> Type.t)) :: c2) @ c1) *)

(* (alpha_i, t_i) (i=0, 1, ... , n-1) maintains a property that forall i, alpha_i does not occur in t_j for all j. *)
and unify : constraint_t list -> unit =
 (* let rec compose (alpha, t) (g : Type.t Substitutes.t) : Type.t Substitutes.t
        =
      let apply (alpha, t) ((beta, t') : subst_t) : subst_t =
        (beta, Type.subst t' alpha t)
      in
      match g with
      | [] -> [ (alpha, t) ]
      | (beta, ((`Int | `Bool | `Func _) as u)) :: g' ->
          (beta, u) :: compose (apply (beta, u) f) (List.map (apply (beta, u)) g')
      | (beta, (`TypeVar _ as gamma)) :: g' ->
          if alpha = gamma then
            apply (beta, gamma) (beta, t) :: compose (apply (beta, gamma) f) g'
          else if beta = gamma then
            (beta, gamma) :: compose (apply (beta, gamma) f) g'
          else (beta, gamma) :: compose (apply (beta, gamma) f) g'
    in *)
 fun (cs : constraint_t list) ->
  let rec unify' (tau, nu) =
    let tau = UnionFind.find tau |> UnionFind.represent
    and nu = UnionFind.find nu |> UnionFind.represent in
    match (tau, nu) with
    | `Int, `Int | `Bool, `Bool | `Unit, `Unit -> ()
    | `Func (a, b), `Func (a', b') ->
        unify' (a, a');
        unify' (b, b')
    | `Tuple ts, `Tuple ts' ->
        if List.length ts <> List.length ts' then
          raise (BadConstraintError (tau, nu))
        else List.iter2 (fun t t' -> unify' (t, t')) ts ts'
    | c, (`TypeVar _ as alpha) | (`TypeVar _ as alpha), c ->
        UnionFind.merge alpha c
    | _ -> raise (BadConstraintError (tau, nu))
  in
  cs |> List.iter unify'

(* match cs with
    | (`Int, `Int) :: cs' | (`Bool, `Bool) :: cs' | (`Unit, `Unit) :: cs' ->
       unify cs'
   | (`Func (a, b), `Func (a', b')) :: cs' -> unify ((a, a') :: (b, b') :: cs')
   (* | (`DFunc (a, b), `DFunc (a', b')) :: cs' ->
       unify ((a, a') :: (b, b') :: cs') *)
   | (t, (`TypeVar _ as alpha)) :: cs' | ((`TypeVar _ as alpha), t) :: cs' -> (
       if alpha = t then unify cs'
       else if alpha |> Type.occurs_in t then
         raise (RecursiveOccurenceError (alpha, t))
       else
         match t with
         | `TypeVar _ as beta ->
             if Substs.UFSet.f alpha <> Substs.UFSet.f beta then
               Substs.UFSet.merge alpha beta;
             unify cs'
         | _ ->
             let substs' =
               cs'
               |> List.map (fun (lhs, rhs) ->
                      (Type.subst lhs alpha t, Type.subst rhs alpha t))
               |> unify
             in
             assert (not (Substitutes.mem alpha substs'));
             substs' |> Substitutes.add alpha t)
   | (t1, t2) :: _ -> raise (BadConstraintError (t1, t2)) *)

let string_of_constraints c =
  c
  |> List.map (fun (t1, t2) -> (Type.string_of t1, Type.string_of t2))
  |> List.map (fun (s1, s2) -> Printf.sprintf "%s = %s" s1 s2)
  |> String.concat "; " |> Printf.sprintf "[%s]"

let infer_cexp env (e : Expr.t) =
  let (t : Type.t), (c : constraint_t list) = infer_expr env e in
  unify c;
  if Debug.debug_flag then (
    Printf.printf "in infer_cexp (e: %s): \n" (Expr.string_of_expr e);
    Printf.printf "type=%s\n" (Type.string_of t);
    Printf.printf "constraints=%s\n" (string_of_constraints c);
    Printf.printf "father=%s\n" UnionFind.(string_of_father ())
    (*Printf.printf "subst=[%s]\n" (Substs.Substitutes.string_of substs)*));
  let t' = UnionFind.apply t in
  (try assert (UnionFind.apply t' = t')
   with e ->
     Printf.printf "t' = %s\n" (Type.string_of t');
     Printf.printf "apply t' = %s\n" (Type.string_of (UnionFind.apply t'));
     Printf.printf "apply t' = %s\n" (Type.string_of (UnionFind.apply t' |> UnionFind.apply));
     raise e);

  let env' = SchemaEnv.map UnionFind.apply_schema env in
  (t', env')

let infer_command (env : SchemaEnv.t) (cmd : Expr.t Command.command) :
    Schema.schema list * SchemaEnv.t =
  match cmd with
  | CExp e ->
      let t, env = infer_cexp env e in
      ([ Schema.schema Type.TypeVarSet.empty t ], env)
  | CDecls (names, exprs) ->
      let ss =
        exprs
        |> List.map (fun e ->
               let t, c = infer_expr env e in
               if Debug.debug_flag then (
                 Printf.printf "in infer_command (e: %s): \n"
                   (Expr.string_of_expr e);
                 Printf.printf "type=%s\n" (Type.string_of t);
                 Printf.printf "constraints=%s\n" (string_of_constraints c);
                 Printf.printf "father=%s\n" UnionFind.(string_of_father ()));
               let s = generalize c env t in
               s)
      in
      let env' = env |> SchemaEnv.extends names ss in
      (ss, env')
  | CRecDecls (names, es) ->
      let typevars =
        List.init (List.length names) (fun _ ->
            let alpha = Type.new_typevar () in
            alpha)
      in
      let schemas : Schema.schema list =
        List.map
          (fun alpha ->
            let polys = Type.TypeVarSet.singleton alpha
            and body :> Type.t = alpha in
            Schema.schema polys body)
          typevars
      in
      let schema_env' = env |> SchemaEnv.extends names schemas in
      let t1s, c1s = List.map (infer_expr schema_env') es |> List.split in
      let c1s' = List.rev c1s |> List.concat in
      let g = generalize c1s' schema_env' in
      let s1s = t1s |> List.map (fun t -> g t) in
      (s1s, env |> SchemaEnv.extends names s1s)
