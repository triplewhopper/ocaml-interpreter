exception DuplicateVariableName of string
exception UnboundVariable of string
exception InvalidLetRecRhsInternal
exception InvalidLetRecRhs of Expr.t


let check_linearity ((names, _) : (string, 'a) Bindings.t) =
  let h = Hashtbl.create (List.length names) in
  names
  |> List.iter (fun name ->
         if Hashtbl.mem h name then raise (DuplicateVariableName name)
         else Hashtbl.add h name ())


let default_transform f e =
  match e with
  | `EConstInt _ | `EConstBool _ | `EConstUnit | `EVar _ -> e
  | `EBinaryOp (op, e1, e2) ->
      let e1' = f e1 in
      let e2' = f e2 in
      if e1' == e1 && e2' == e2 then e else `EBinaryOp (op, e1', e2')
  | `EUnaryOp (op, e1) ->
      let e1' = f e1 in
      if e1' == e1 then e else `EUnaryOp (op, e1')
  | `EIf (e1, e2, e3) ->
      let e1' = f e1 in
      let e2' = f e2 in
      let e3' = f e3 in
      if e1' == e1 && e2' == e2 && e3' == e3 then e else `EIf (e1', e2', e3')
  | `ECall (e1, e2) ->
      let e1' = f e1 in
      let e2' = f e2 in
      if e1 == e1' && e2 == e2' then e else `ECall (e1', e2')
  | `EFun (id, x, e2) ->
      let e2' = f e2 in
      if e2' == e2 then e else `EFun (id, x, e2')
  | `EDFun (id, x, e2) ->
      let e2' = f e2 in
      if e2' == e2 then e else `EDFun (id, x, e2')
  | `ELet ((xs, es), e2) ->
      let es' = List.map f es in
      let e2' = f e2 in
      if List.for_all2 ( == ) es es' && e2' == e2 then e
      else `ELet ((xs, es'), e2')
  | `ELetRec ((xs, es), e2) ->
      let es' = List.map f es in
      let e2' = f e2 in
      if List.for_all2 ( == ) es' es && e2' == e2 then e
      else `ELetRec ((xs, es'), e2')

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
  | `ECall (e1, e2) ->
      f e1;
      f e2
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

let rec expand_logical_operator e =
  let f = expand_logical_operator in
  match e with
  | `EBinaryOp ("||", e1, e2) ->
      let e1' = f e1 in
      let e2' = f e2 in
      `EIf (e1', `EConstBool true, e2')
  | `EBinaryOp ("&&", e1, e2) ->
      let e1' = f e1 in
      let e2' = f e2 in
      `EIf (e1', e2', `EConstBool false)
  | _ -> default_transform f e

let rec expand_binary_operator e =
  let f = expand_binary_operator in
  match e with
  | `EBinaryOp (op, e1, e2) -> `ECall (`ECall (`EVar op, f e1), f e2)
  | _ -> default_transform f e

let rec expand_unary_operator e =
  let f = expand_unary_operator in
  match e with
  | `EUnaryOp (op, e1) -> `ECall (`EVar op, f e1)
  | _ -> default_transform f e

(* let rec expand_dfun env e =
   match e with
   | `Var x -> (match Env.lookup x env with
   | Value.VDFun (_, x, fv) -> List.fold_right (fun x e -> `ECall (x, e)) fv (`EVar x)) *)

let rec check_unbound_variables env e : unit =
  let f = check_unbound_variables env in
  match e with
  | `EFun (_, x, e2) -> check_unbound_variables (x :: env) e2
  | `EDFun (_, x, e2) -> 
    (* Printf.printf "free vars of %s = [%s]\n" (Expr.string_of_expr e) (Expr.free_vars e |> Expr.StringSet.elements |> String.concat ", "); *)
    check_unbound_variables (x :: (Expr.free_vars e|> Expr.StringSet.elements)@env) e2
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

(* let rec check_reference env e : unit =
   let f = check_reference env in
   match e with
   | `EFun (_, x, e2) -> check_reference (env |> Env.extend x (ref true)) e2
   | `ELet ((vars, e1s), e2) ->
       List.iter f e1s;
       let env' =
         List.fold_left
           (fun env0 var -> env0 |> Env.extend var (ref true))
           env vars
       in
       check_reference env' e2
   | `ELetRec ((vars, es), body) ->
       (* let rec var1=e1 and var2=e2 ... and var_N=e_N in body *)
       let env' =
         List.fold_left
           (fun env0 var -> env0 |> Env.extend var (ref false))
           env vars
       in
       List.iter
         (fun e ->
           match e with
           | `EFun _ -> ()
           | _ -> (
               try check_reference env' e
               with InvalidLetRecRhsInternal -> raise (InvalidLetRecRhs e)))
         es;
       List.iter
         (fun var ->
           let v = env' |> Env.lookup var in
           assert (!v = false);
           v := true)
         vars;
       List.iter
         (fun e ->
           match e with
           | `EFun _ -> (
               try check_reference env' e
               with InvalidLetRecRhsInternal -> raise (InvalidLetRecRhs e))
           | _ -> ())
         es;
       check_reference env' body
   | `EVar x -> (
       try
         match !(Env.lookup x env) with
         | true -> ()
         | false -> raise InvalidLetRecRhsInternal
       with Not_found -> assert false)
   | _ -> default_check f e *)

let check_command debug_flag (env : Schema.SchemaEnv.t) (cmd : Command.command)
    =
  match cmd with
  | CExp e ->
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e;
      check_bindings_uniqueness e
  | CDecls (names, exprs) ->
      if debug_flag then
        Printf.printf "number of decl: %d\n" (List.length names);
      let e' = `ELet ((names, exprs), `EConstUnit) in
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e';
      check_bindings_uniqueness e'
  | CRecDecls (names, es) ->
      if debug_flag then
        Printf.printf "number of rec decl: %d\n" (List.length names);
      let e' = `ELetRec ((names, es), `EConstUnit) in
      check_unbound_variables (env.env |> List.map (fun (k, _) -> k)) e';
      check_bindings_uniqueness e'

let transform_command debug_flag (s_env : Schema.SchemaEnv.t)
    (env : Value.value Env.t) (cmd : Command.command) =
  match cmd with
  | CExp e ->
    let _ = debug_flag, s_env, env in
      let e' =
        e |> expand_logical_operator |> expand_binary_operator
        |> expand_unary_operator
      in
      Command.CExp e'
  | CDecls (names, exprs) ->
      Command.CDecls
        ( names,
          exprs
          |> List.map (fun e ->
                 e |> expand_logical_operator |> expand_binary_operator
                 |> expand_unary_operator) )
  | CRecDecls (names, es) ->
      Command.CRecDecls
        ( names,
          es
          |> List.map (fun e ->
                 e |> expand_logical_operator |> expand_binary_operator
                 |> expand_unary_operator) )
