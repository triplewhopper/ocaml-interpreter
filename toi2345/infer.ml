type constraint_t = Type.t * Type.t

module SchemaEnv = Schema.SchemaEnv
module TypeHashtbl = Type.TypeHashtbl

exception RecursiveOccurenceError of Type.typevar_t * Type.t
exception BadConstraintError of Type.t * Type.t

let ( = ) : int -> int -> bool =
  ( = ) (* prevent from using `=' between Type.t values *)

module UnionFind : sig
  val find : Type.t -> Type.t
  val merge : Type.t -> Type.t -> unit
  val represent : Type.t -> Type.t
  val apply : Type.t -> Type.t
  val apply_schema : Schema.schema -> Schema.schema
  val string_of_father : unit -> string
  val backup : unit -> unit
  val restore : unit -> unit
end = struct
  let father : Type.t TypeHashtbl.t ref = ref (TypeHashtbl.create 0)
  let rk : int TypeHashtbl.t ref = ref (TypeHashtbl.create 0)
  let representative : Type.t TypeHashtbl.t ref = ref (TypeHashtbl.create 0)
  let father_backup = ref None
  let rk_backup = ref None
  let representative_backup = ref None

  let backup () =
    father_backup := Some (TypeHashtbl.copy !father);
    rk_backup := Some (TypeHashtbl.copy !rk);
    representative_backup := Some (TypeHashtbl.copy !representative)

  let restore () =
    father := Option.get !father_backup;
    rk := Option.get !rk_backup;
    representative := Option.get !representative_backup;
    father_backup := None;
    rk_backup := None;
    representative_backup := None

  let rank x =
    match TypeHashtbl.find_opt !rk x with
    | Some r -> r
    | None ->
        TypeHashtbl.add !rk x 0;
        0

  let rec find x =
    match TypeHashtbl.find_opt !father x with
    | Some x' ->
        if Type.equal x x' then x
        else
          let f' = find x' in
          TypeHashtbl.replace !father x f';
          f'
    | None ->
        TypeHashtbl.add !father x x;
        if not (Type.is_typevar x) then TypeHashtbl.add !representative x x;
        x

  let represent x =
    let f = find x in
    match TypeHashtbl.find_opt !representative f with
    | Some x' -> x'
    | None -> f

  let apply t =
    let table = TypeHashtbl.create 0 in
    let rec apply' t = Type.memo table apply'' t
    and apply'' t =
      match t with
      (* | `Int -> `Int
         | `Bool -> `Bool
         | `Unit -> `Unit
         | `Func (_, t1, t2) -> Type.func (apply' t1, apply' t2)
         | `Tuple (_, ts) -> Type.tuple (List.map apply' ts) *)
      | `TyCon (con, _, ts) -> Type.constr con (List.map apply' ts)
      | `TypeVar _ as beta ->
          let t = represent beta in
          if not (Type.equal beta t) then
            if beta |> Type.occurs_in t then
              raise (RecursiveOccurenceError (beta, t))
            else apply' t
          else t
    in
    let t' = apply' t in
    assert (Type.equal t' (apply' t));
    t'

  let apply_schema (s : Schema.schema) =
    let table = TypeHashtbl.create 0 in
    let rec apply' t = Type.memo table apply'' t
    and apply'' t =
      match t with
      (* | `Int -> `Int
         | `Bool -> `Bool
         | `Unit -> `Unit
         | `Func (_, t1, t2) -> Type.func (apply' t1, apply' t2)
         | `Tuple (_, ts) -> Type.tuple (List.map apply' ts) *)
      | `TyCon (con, _, ts) -> Type.constr con (List.map apply' ts)
      | `TypeVar _ as beta ->
          if Type.TypeVarSet.mem beta s.fv then
            let t = represent beta in
            if not (Type.equal beta t) then
              if beta |> Type.occurs_in t then
                raise (RecursiveOccurenceError (beta, t))
              else apply' t
            else t
          else beta
    in
    let body' = apply' s.body in
    assert (Type.equal body' (apply' body'));
    Schema.schema s.polys body'

  let merge x1 x2 =
    let f1, f2 = (find x1, find x2) in
    if not (Type.equal f1 f2) then (
      if not (Type.is_typevar f1) then TypeHashtbl.replace !representative f2 f1;
      if not (Type.is_typevar f2) then TypeHashtbl.replace !representative f1 f2;
      let c = rank f1 - rank f2 in
      if c > 0 then TypeHashtbl.replace !father f2 f1
      else TypeHashtbl.replace !father f1 f2;
      if c = 0 then
        let rk_f2 = TypeHashtbl.find !rk f2 in
        TypeHashtbl.replace !rk f2 (rk_f2 + 1))

  let string_of_father () =
    let groups = TypeHashtbl.create 0 in
    !father |> TypeHashtbl.to_seq_keys
    |> Seq.iter (fun alpha ->
           match TypeHashtbl.find_opt groups (find alpha) with
           | Some vs -> vs := alpha :: !vs
           | None -> TypeHashtbl.add groups (find alpha) (ref [ alpha ]));
    groups |> TypeHashtbl.to_seq
    |> Seq.map (fun (_, (g : Type.t list ref)) ->
           !g |> List.map Type.string_of |> String.concat ", "
           |> Printf.sprintf "[%s]")
    |> List.of_seq |> String.concat "; " |> Printf.sprintf "[%s]"
end

let instantiate (s : Schema.schema) : Type.t =
  let table = Hashtbl.create (Type.TypeVarSet.cardinal s.polys) in
  Type.TypeVarSet.iter
    (fun alpha -> Hashtbl.add table alpha (Type.new_typevar () :> Type.t))
    s.polys;
  let memory = TypeHashtbl.create 0 in
  let rec instantiate' (t : Type.t) : Type.t = Type.memo memory instantiate'' t
  and instantiate'' = function
    (* | `Int -> `Int
       | `Bool -> `Bool
       | `Unit -> `Unit
       | `Func (_, t1, t2) as f ->
           if Type.TypeVarSet.disjoint (Type.fv f) s.polys then f
           else Type.func (instantiate' t1, instantiate' t2)
       | `Tuple (_, ts) as tuple ->
           assert (List.length ts = 2);
           if Type.TypeVarSet.disjoint (Type.fv tuple) s.polys then tuple
           else Type.tuple (List.map instantiate' ts) *)
    | `TyCon (con, _, ts) as typ ->
        if Type.TypeVarSet.disjoint (Type.fv typ) s.polys then typ
        else Type.constr con (List.map instantiate' ts)
    | `TypeVar _ as alpha ->
        if Type.TypeVarSet.mem alpha s.polys then Hashtbl.find table alpha
        else alpha
  in
  instantiate' s.body

let unify : constraint_t list -> unit =
 fun (cs : constraint_t list) ->
  let rec unify' (tau, nu) =
    let tau = UnionFind.find tau in
    let tau = tau |> UnionFind.represent in
    let nu = UnionFind.find nu in
    let nu = nu |> UnionFind.represent in

    match (tau, nu) with
    (* | `Int, `Int | `Bool, `Bool | `Unit, `Unit -> ()
       | `Func (_, a, b), `Func (_, a', b') ->
           unify' (a, a');
           unify' (b, b')
       | `Tuple (_, ts), `Tuple (_, ts') ->
           if List.length ts <> List.length ts' then
             raise (BadConstraintError (tau, nu))
           else List.iter2 (fun t t' -> unify' (t, t')) ts ts' *)
    | `TyCon (con, _, ts), `TyCon (con', _, ts') ->
        if con <> con' then raise (BadConstraintError (tau, nu))
        else if List.length ts <> List.length ts' then
          raise (BadConstraintError (tau, nu))
        else List.iter2 (fun t t' -> unify' (t, t')) ts ts'
    | c, (`TypeVar _ as alpha) | (`TypeVar _ as alpha), c ->
        UnionFind.merge alpha c
  in

  let res = cs |> List.rev |> List.iter unify' in
  res

let string_of_constraints c =
  c
  |> List.map (fun (t1, t2) -> (Type.string_of t1, Type.string_of t2))
  |> List.map (fun (s1, s2) -> Printf.sprintf "%s = %s" s1 s2)
  |> String.concat "; " |> Printf.sprintf "[%s]"

let generalize (c : constraint_t list) =
  unify c;
  fun (env : SchemaEnv.t) ->
    let env' = SchemaEnv.map UnionFind.apply_schema env in
    fun (t : Type.t) ->
      let typ = UnionFind.apply t in
      assert (Type.equal typ (UnionFind.apply typ));
      let polys = Type.TypeVarSet.diff (Type.fv typ) env'.fv in
      let s = Schema.schema polys typ in
      if Options.debug_flag then (
        Printf.printf "schema_env = %s\n" (Schema.string_of_senv env');
        Printf.printf "constraints = %s\n" (string_of_constraints c);
        Printf.printf "father=%s\n" (UnionFind.string_of_father ());
        Printf.printf "t = %s\n" (Type.string_of t);
        Printf.printf "generalize %s to %s\n" (Type.string_of typ)
          (Schema.string_of_schema s));
      s

let rec infer_expr (schema_env : SchemaEnv.t) e : Type.t * constraint_t list =
  match e with
  | `EConstInt _ -> (Type.ty_int, [])
  | `EConstBool _ -> (Type.ty_bool, [])
  | `EConstUnit -> (Type.ty_unit, [])
  | `EVar x -> (
      try
        let s = schema_env |> SchemaEnv.lookup x in
        let typ = s |> instantiate in
        if Options.debug_flag then
          Printf.printf "instantiate %s : %s to  %s\n" x
            (Schema.string_of_schema s)
            (Type.string_of typ);
        (typ, [])
      with Not_found -> raise (Transform.UnboundVariable x))
  | `EIf (e1, e2, e3) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let t3, c3 = infer_expr schema_env e3 in
      (t2, ((t2, t3) :: c3) @ c2 @ ((t1, Type.ty_bool) :: c1))
  | `EFun (_, var, body) ->
      let alpha = Type.new_typevar () in
      let s_alpha = Schema.from_monomorphic_typevar alpha in
      let env' = schema_env |> SchemaEnv.extend var s_alpha in
      let t, c = infer_expr env' body in
      (Type.func ((alpha :> Type.t), t), c)
  | `ECall (e1, e2) ->
      let t1, c1 = infer_expr schema_env e1 in
      let t2, c2 = infer_expr schema_env e2 in
      let alpha = Type.new_typevar () in
      let alpha' :> Type.t = alpha in
      (alpha', ((t1, Type.func (t2, alpha')) :: c2) @ c1)
  | `ETuple es ->
      let ts, cs = List.map (infer_expr schema_env) es |> List.split in
      let ts' = ts and cs' = cs |> List.rev |> List.concat in
      (Type.tuple ts', cs')
  | `EList es -> (
      match es with
      | [] -> (Type.ty_list (Type.new_typevar () :> Type.t), [])
      | e :: es ->
          let t, c = infer_expr schema_env e in
          let ts, cs = List.map (infer_expr schema_env) es |> List.split in
          let cs' = c :: cs |> List.rev |> List.concat in
          (Type.ty_list t, List.map (fun t' -> (t, t')) ts @ cs'))
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
  | `ELetRec ((names, funcs), e2) ->
      let schemas : Schema.schema list =
        List.init (List.length names) (fun _ -> Type.new_typevar ())
        |> List.map Schema.from_monomorphic_typevar
      in
      let schema_env' = schema_env |> SchemaEnv.extends names schemas in
      let t1s, c1s =
        List.map (infer_expr schema_env') funcs
        |> List.fold_left2
             (fun (t1s, c1s) name (t, cs) ->
               let cs' =
                 let t' = schema_env' |> SchemaEnv.lookup name |> instantiate in
                 (t', t) :: cs
               in
               (t :: t1s, cs' :: c1s))
             ([], []) names
      in
      let t1s = t1s |> List.rev in
      let c1s' = c1s |> List.concat in
      let g = generalize c1s' schema_env in
      let s1s = t1s |> List.map (fun t -> g t) in
      let s2, c2 = infer_expr (schema_env |> SchemaEnv.extends names s1s) e2 in
      (s2, c2 @ c1s')

let infer_cexp env (e : Expr.t) =
  let (t : Type.t), (c : constraint_t list) = infer_expr env e in
  unify c;
  if Options.debug_flag then (
    Printf.printf "in infer_cexp (e: %s): \n" (Expr.string_of_expr e);
    Printf.printf "type=%s\n" (Type.string_of t);
    Printf.printf "constraints=%s\n" (string_of_constraints c);
    Printf.printf "father=%s\n" UnionFind.(string_of_father ()));
  let t' = UnionFind.apply t in
  let env' = SchemaEnv.map UnionFind.apply_schema env in
  (t', env')

let infer_command' (env : SchemaEnv.t) (cmd : Expr.t Command.command) :
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
               if Options.debug_flag then (
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
      let schemas : Schema.schema list =
        List.init (List.length names) (fun _ -> Type.new_typevar ())
        |> List.map Schema.from_monomorphic_typevar
      in
      let schema_env' = env |> SchemaEnv.extends names schemas in
      let t1s, c1s =
        List.map (infer_expr schema_env') es
        |> List.fold_left2
             (fun (t1s, c1s) name (t, cs) ->
               let cs' =
                 let t' = schema_env' |> SchemaEnv.lookup name |> instantiate in
                 (t', t) :: cs
               in
               (t :: t1s, cs' :: c1s))
             ([], []) names
      in
      let t1s = List.rev t1s in
      let c1s' = c1s |> List.concat in
      let g = generalize c1s' env in
      let s1s = t1s |> List.map (fun t -> g t) in
      (s1s, env |> SchemaEnv.extends names s1s)

let infer_command (env : SchemaEnv.t) (cmd : Expr.t Command.command) :
    Schema.schema list * SchemaEnv.t =
  UnionFind.backup ();
  try infer_command' env cmd
  with e ->
    UnionFind.restore ();
    raise e
