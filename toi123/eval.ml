type value = Value.value
type expr = Expr.t
type 'a command = 'a Command.command
type ('a, 'b) bindings = ('a, 'b) Bindings.t

exception NotCallable of value

let string_of_env env =
  Printf.sprintf "{%s}"
    (env
    |> List.filter_map (fun (x, v) ->
           match !v with
           | Some (Value.VBuiltinFun _) | None -> None
           | Some v -> Some (Printf.sprintf "%s=%s" x (Value.string_of_value v)))
    |> String.concat ", ")

let rec eval_expr (env : value option ref Env.t) (e : expr) : value =
  match e with
  | `EConstInt i -> VInt i
  | `EConstBool b -> VBool b
  | `EConstUnit -> VUnit
  | `EVar x -> (
      try
        match !(Env.lookup x env) with
        | Some v -> v
        | None -> raise (Transform.InvalidLetRecRhs (`EVar x))
      with Not_found ->
        (* Printf.printf "env=%s\n" (string_of_env env); *)
        raise (Transform.UnboundVariable x))
  | `ECall (e1, e2) -> (
      (* Printf.printf "--> %s\n" (Expr.string_of_expr e); *)
      (* Printf.printf "env=%s\n" (env |> string_of_env); *)
      let v1 = eval_expr env e1 in
      let v2 = eval_expr env e2 in
      match v1 with
      | VFunc (x, e', oenv) ->
          eval_expr (!oenv |> Env.extend x (ref (Some v2))) e'
      | VBuiltinFun (_, f) -> f v2
      | v -> raise (NotCallable v))
  | `ETuple es ->
      let vs = List.map (eval_expr env) es in
      VTuple vs
  | `EList es ->
      let vs = List.map (eval_expr env) es in
      VList vs
  | `EMatch (e, qs) -> (
      let v = eval_expr env e in
      qs
      |> List.fold_left
           (fun acc (p, e) ->
             if Option.is_some acc then acc
             else
               Match.find_match p v
               |> Option.map (fun bindings ->
                      let names, vs = bindings |> List.split in
                      let values =
                        List.rev_map Option.some vs |> List.rev_map ref
                      in
                      let env' = env |> Env.extends names values in
                      eval_expr env' e))
           None
      |> function
      | Some v -> v
      | None -> raise Match.MatchFailed)
  | `EFun (_, var, body) -> VFunc (var, body, ref env)
  | `ELet ((vars, e1s), e2) ->
      let v1s = List.map (eval_expr env) e1s in
      let env' =
        List.fold_left2
          (fun env0 var v -> env0 |> Env.extend var (ref (Some v)))
          env vars v1s
      in
      eval_expr env' e2
  | `ELetRec ((vars, es), body) ->
      (* let rec var1=e1 and var2=e2 ... and var_N=e_N in body *)
      let env' =
        List.fold_left
          (fun env0 var -> env0 |> Env.extend var (ref None))
          env vars
      in
      let vs = List.map (eval_expr env') es in
      List.iter2
        (fun var rhs ->
          let v = env' |> Env.lookup var in
          assert (Option.is_none !v);
          v := Some rhs)
        vars vs;
      eval_expr env' body
  | `EIf (e1, e2, e3) -> (
      let v1 = eval_expr env e1 in
      match v1 with
      | VBool true -> eval_expr env e2
      | VBool false -> eval_expr env e3
      | _ -> raise (Value.TypeError (Value.string_of_value v1)))

type eval_result_t =
  | Immediate of value option
  | Named of string list * value list option

let eval_command env (c : 'a command) =
  match c with
  | CExp e ->
      if Options.inference_only then (
        Printf.eprintf "type inference done.\n";
        flush stderr;
        (Immediate None, env))
      else
        let v = eval_expr env e in
        (Immediate (Some v), env)
  | CDecls (names, es) ->
      if Options.inference_only then (
        Printf.eprintf "type inference done.\n";
        flush stderr;
        (Named (names, None), env))
      else
        let vs = List.map (eval_expr env) es in
        let vs' = vs |> List.map (fun v -> ref (Some v)) in
        let env' = env |> Env.extends names vs' in
        (Named (names, Some vs), env')
  | CRecDecls (names, es) ->
      if Options.inference_only then (
        Printf.eprintf "type inference done.\n";
        flush stderr;
        (Named (names, None), env))
      else
        let env' =
          List.fold_left
            (fun env0 var -> env0 |> Env.extend var (ref None))
            env names
        in
        let vs = List.map (eval_expr env') es in
        List.iter2
          (fun var rhs ->
            let v = env' |> Env.lookup var in
            assert (Option.is_none !v);
            v := Some rhs)
          names vs;
        (Named (names, Some vs), env')
