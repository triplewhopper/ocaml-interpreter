exception DuplicateVariableName of string
exception UnboundVariable of string
exception InvalidLetRecRhsInternal
exception InvalidLetRecRhs of Expr.t0

let check_linearity ((names, _) : (string, 'a) Bindings.t) =
  let h = Hashtbl.create (List.length names) in
  names
  |> List.iter (fun name ->
         if Hashtbl.mem h name then raise (DuplicateVariableName name)
         else Hashtbl.add h name ())

let default_check f e =
  match e with
  | `EConstInt _ | `EConstBool _ | `EConstUnit | `EVar _ -> ()
  | `EBinaryOp (_, e1, e2) ->
      f e1;
      f e2
  | `EUnaryOp (_, e1) -> f e1
  | `EIf (e1, e2, e3) ->
      f e1;
      f e2;
      f e3
  | `ECall (e1, e2)  ->
      f e1;
      f e2
  | `ETuple es | `EList es ->
      List.iter f es
  | `EFun (_, _, e2) -> f e2
  | `EDFun (_, _, e2) -> f e2
  | `ELet ((_, es), e2) ->
      List.iter f es;
      f e2
  | `ELetRec ((_, es), e2) ->
      List.iter f es;
      f e2

let rec check_bindings_uniqueness e =
  let f = check_bindings_uniqueness in
  match e with
  | `ELet ((xs, es), e2) ->
      check_linearity (xs, es);
      List.iter f es;
      f e2
  | `ELetRec ((xs, es), e2) ->
      check_linearity (xs, es);
      List.iter f es;
      f e2
  | _ -> default_check f e

let rec expand_operators (e : Expr.t0) : Expr.t =
  let f = expand_operators in
  match e with
  | `EConstInt _ as e -> e
  | `EConstBool _ as e -> e
  | `EConstUnit as e -> e
  | `EVar _ as e -> e
  | `EBinaryOp ("||", e1, e2) -> `EIf (f e1, `EConstBool true, f e2)
  | `EBinaryOp ("&&", e1, e2) -> `EIf (f e1, f e2, `EConstBool false)
  | `EBinaryOp (op, e1, e2) -> `ECall (`ECall (`EVar op, f e1), f e2)
  | `EUnaryOp (op, e1) -> `ECall (`EVar op, f e1)
  | `EIf (e1, e2, e3) -> `EIf (f e1, f e2, f e3)
  | `ECall (e1, e2) -> `ECall (f e1, f e2)
  | `ETuple es -> `ETuple (List.map f es)
  | `EList es -> `EList (List.map f es)
  | `EFun (id, x, e2) -> `EFun (id, x, f e2)
  | `ELet ((xs, es), e2) -> `ELet ((xs, List.map f es), f e2)
  | `ELetRec ((xs, es), e2) -> `ELetRec ((xs, List.map f es), f e2)

let rec check_unbound_variables env e =
  let f = check_unbound_variables env in
  match e with
  | `EFun (_, x, e2) -> check_unbound_variables (x :: env) e2
  | `ELet ((vars, e1s), e2) ->
      List.iter f e1s;
      let env' = vars @ env in
      check_unbound_variables env' e2
  | `ELetRec ((vars, es), body) ->
      let env' = vars @ env in
      List.iter (check_unbound_variables env') es;
      List.iter
        (fun e ->
          match e with `EFun _ -> () | _ -> raise (InvalidLetRecRhs e))
        es;
      check_unbound_variables env' body
  | `EVar x -> if not (List.mem x env) then raise (UnboundVariable x) else ()
  | _ -> default_check f e

let check_command (env : Schema.SchemaEnv.t)
    (cmd : Expr.t0 Command.command) =
  match cmd with
  | CExp e ->
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e;
      check_bindings_uniqueness e
  | CDecls (names, exprs) ->
      if Options.debug_flag then
        Printf.printf "number of decl: %d\n" (List.length names);
      let e' = `ELet ((names, exprs), `EConstUnit) in
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e';
      check_bindings_uniqueness e'
  | CRecDecls (names, es) ->
      if Options.debug_flag then
        Printf.printf "number of rec decl: %d\n" (List.length names);
      let e' = `ELetRec ((names, es), `EConstUnit) in
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e';
      check_bindings_uniqueness e'

let transform_command (_ : Schema.SchemaEnv.t)
    (cmd : Expr.t0 Command.command) : Expr.t Command.t
    =
  match cmd with
  | CExp e ->
      Command.CExp (expand_operators e)
  | CDecls (names, exprs) ->
      Command.CDecls (names, exprs |> List.map expand_operators)
  | CRecDecls (names, es) ->
      Command.CRecDecls (names, es |> List.map expand_operators)
