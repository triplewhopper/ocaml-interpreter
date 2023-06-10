type expr = Expr.t
type constraint_t = Type.t * Type.t
type subst_t = Type.typevar_t * Type.t

module SchemaEnv = Schema.SchemaEnv

exception RecursiveOccurenceError of Type.typevar_t * Type.t
exception BadConstraintError of Type.t * Type.t

module Substitutes = Map.Make (struct
  type t = Type.typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)

let simplify_subst (substs : Type.t Substitutes.t) =
  let substs' =
    substs |> Substitutes.to_seq
    |> Seq.filter (fun (alpha, t) ->
           match t with
           | #Type.typevar_t as beta -> Type.UFSet.f alpha = Type.UFSet.f beta
           | _ -> true)
  in
  assert (
    substs'
    |> Seq.for_all (fun (_, t) ->
           match t with #Type.typevar_t -> false | _ -> true));

  substs'
  |> Seq.map (fun (alpha, t) -> (Type.UFSet.f alpha, Type.UFSet.simplify t))
  |> Substitutes.of_seq

let apply_subst (substs : Type.t Substitutes.t) typ =
  let fv = Type.fv typ in
  let intersection =
    if Type.TypeVarSet.cardinal fv < Substitutes.cardinal substs then
      Type.TypeVarSet.fold
        (fun x acc ->
          match Substitutes.find_opt x substs with
          | None -> acc
          | Some v -> Substitutes.add x v acc)
        fv Substitutes.empty
    else Substitutes.filter (fun k _ -> Type.TypeVarSet.mem k fv) substs
  in
  Substitutes.fold (fun alpha t typ -> Type.subst typ alpha t) intersection typ

let apply_subst_schema (substs : Type.t Substitutes.t) (s : Schema.schema) =
  let fv = s.fv in
  let intersection =
    if Type.TypeVarSet.cardinal fv < Substitutes.cardinal substs then
      Type.TypeVarSet.fold
        (fun x acc ->
          match Substitutes.find_opt x substs with
          | None -> acc
          | Some v -> Substitutes.add x v acc)
        fv Substitutes.empty
    else Substitutes.filter (fun k _ -> Type.TypeVarSet.mem k fv) substs
  in
  if Substitutes.is_empty intersection then s
  else
    Substitutes.fold
      (fun alpha t typ -> Type.subst typ alpha t)
      intersection s.body
    |> Schema.schema s.polys

let infer_ii_i (t1 : Type.t) (c1 : constraint_t list) (t2 : Type.t)
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

let infer_binaryOp (_ : SchemaEnv.t) (op : string) = Env.lookup op !binaryOpEnv

let rec generalize (c : constraint_t list) =
  let substs = unify c |> simplify_subst in
  fun (env : SchemaEnv.t) ->
    let env' = SchemaEnv.map (apply_subst_schema substs) env in
    (* Printf.printf "env'= {%s}\n" (env.env |> List.map (fun (k, v) -> Printf.sprintf "%s: %s" k (Type.string_of_schema v))|> String.concat "; "); *)
    fun (t : Type.t) ->
      let typ = apply_subst substs t in
      (* assert (Type.fv typ |> Type.TypeVarSet.is_empty |> not); *)
      (* assert (env'.fv |> Type.TypeVarSet.is_empty); *)
      let polys = Type.TypeVarSet.diff (Type.fv typ) env'.fv in
      (* assert (Type.TypeVarSet.is_empty polys |> not); *)
      (* Printf.printf "polys={%s}\n" ((polys |> Type.TypeVarSet.elements:> Type.t list) |> List.map Type.string_of |> String.concat "; "); *)
      (Schema.schema polys typ, env')

and infer_expr (schema_env : SchemaEnv.t) e : Type.t * constraint_t list =
  match e with
  | `EConstInt _ -> (`Int, [])
  | `EConstBool _ -> (`Bool, [])
  | `EConstUnit -> (`Unit, [])
  | `EVar x -> (
      try
        let s = schema_env |> SchemaEnv.lookup x in
        let typ = s |> Schema.instantiate in
        (typ, [])
      with Not_found -> raise (Transform.UnboundVariable x))
  | `EIf (e1, e2, e3) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let t3, c3 = infer_expr schema_env e3 in
      (t2, ((t2, t3) :: c3) @ c2 @ ((t1, `Bool) :: c1))
  | `EBinaryOp (op, e1, e2) ->
      let t1, c1 = infer_expr schema_env e1 in
      (* assert (s1.polys = []); *)
      let t2, c2 = infer_expr schema_env e2 in
      (* assert (s2.polys = []); *)
      let t, c = infer_binaryOp schema_env op t1 c1 t2 c2 in
      (t, c)
  | `EUnaryOp (_, e) ->
      let t, c = infer_expr schema_env e in
      (`Int, (t, `Int) :: c)
  | `EFun (_, var, body) ->
      let alpha = Type.new_typevar () in
      let s_alpha = Schema.schema Type.TypeVarSet.empty (alpha :> Type.t) in
      let env' = schema_env |> SchemaEnv.extend var s_alpha in
      let t, c = infer_expr env' body in
      (* let substs = unify c in
         let s' = {s with monos=List.filter (fun x -> not (List.mem_assoc x substs)) s.monos; body=apply_subst substs s.body} in
         let env_monos1' = List.filter (fun x -> not (List.mem_assoc x substs)) env_monos1 in
         let typ = apply_subst substs (`Func ((alpha:>Type.t), s.body)) in *)
      (Type.func ((alpha :> Type.t), t), c)
  | `EDFun (_, var, body) ->
      let free_vars = Expr.free_vars e |> Expr.StringSet.elements in
      let alphas =
        Type.new_typevar () :: List.map (fun _ -> Type.new_typevar ()) free_vars
      in
      let s_alphas =
        List.map (Schema.schema Type.TypeVarSet.empty) (alphas :> Type.t list)
      in
      let env' = schema_env |> SchemaEnv.extends (var :: free_vars) s_alphas in
      let t, c = infer_expr env' body in
      (Type.func ((List.hd alphas :> Type.t), t), c)
  | `ECall (e1, e2) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let alpha = Type.new_typevar () in
      let alpha' :> Type.t = alpha in
      (alpha', ((t1, Type.func (t2, alpha')) :: c2) @ c1)
  | `ELet ((names, e1s), e2) ->
      let ss =
        List.map
          (fun e ->
            let t, c = infer_expr schema_env e in
            let s, _ = generalize c schema_env t in
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
      let s1s = t1s |> List.map (fun t -> g t |> fst) in
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
and unify : constraint_t list -> Type.t Substitutes.t =
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
  match cs with
  | [] -> Substitutes.empty
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
        | #Type.typevar_t as beta ->
            if Type.UFSet.f alpha <> Type.UFSet.f beta then
              Type.UFSet.merge alpha beta;
            unify cs'
        | _ ->
            let substs' =
              cs'
              |> List.map (fun (lhs, rhs) ->
                     (Type.subst lhs alpha t, Type.subst rhs alpha t))
              |> unify
            in
            assert (not (Substitutes.mem alpha substs'));
            Substitutes.add alpha t substs')
  | (t1, t2) :: _ -> raise (BadConstraintError (t1, t2))

let infer_cexp debug_flag env e =
  let (t : Type.t), (c : constraint_t list) = infer_expr env e in
  let substs = unify c |> simplify_subst in
  if debug_flag then (
    Printf.printf "in infer_cexp (e: %s): \n" (Expr.string_of_expr e);
    Printf.printf "type=%s\n" (Type.string_of t);
    Printf.printf "constraints=[%s]\n"
      (c
      |> List.map (fun (t1, t2) -> (Type.string_of t1, Type.string_of t2))
      |> List.map (fun (s1, s2) -> Printf.sprintf "%s = %s" s1 s2)
      |> String.concat "; ");
    Printf.printf "father=[%s]\n"
      (Type.UFSet.father |> Hashtbl.to_seq
      |> Seq.map (fun (alpha, _) ->
             ( Type.string_of (alpha :> Type.t),
               Type.string_of (Type.UFSet.f alpha :> Type.t) ))
      |> Seq.map (fun (s1, s2) -> Printf.sprintf "%s : %s" s1 s2)
      |> List.of_seq |> String.concat "; ");
    Printf.printf "subst=[%s]\n"
      (substs |> Substitutes.bindings
      |> List.map (fun (t1, t2) ->
             (Type.string_of (t1 :> Type.t), Type.string_of t2))
      |> List.map (fun (s1, s2) -> Printf.sprintf "%s := %s" s1 s2)
      |> String.concat "; "));

  let t' = apply_subst substs (Type.UFSet.simplify t) in
  let env' = SchemaEnv.map (apply_subst_schema substs) env in
  (t', env')

let infer_command debug_flag (env : SchemaEnv.t) (cmd : Command.command) :
    Schema.schema list * SchemaEnv.t =
  match cmd with
  | CExp e ->
      let t, env = infer_cexp debug_flag env e in
      ([ Schema.schema Type.TypeVarSet.empty t ], env)
  | CDecls (names, exprs) ->
      let ss =
        exprs
        |> List.map (fun e ->
               let t, c = infer_expr env e in
               let s, _ = generalize c env t in
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
      let s1s = t1s |> List.map (fun t -> g t |> fst) in
      (s1s, env |> SchemaEnv.extends names s1s)
