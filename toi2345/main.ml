let debug_flag = false
let () = Printexc.record_backtrace true

let iter3 f xs ys zs =
  let rec iter3' xs ys zs =
    match (xs, ys, zs) with
    | [], [], [] -> ()
    | x :: xs', y :: ys', z :: zs' ->
        f x y z;
        iter3' xs' ys' zs'
    | _ -> ()
  in
  let a, b, c = (List.length xs, List.length ys, List.length zs) in
  if a = b && b = c then iter3' xs ys zs
  else raise (Invalid_argument "different lengths")

let rec read_eval_print (s_env : Infer.SchemaEnv.t) env =
  print_string "# ";
  flush stdout;
  (try
     let cmds = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
     let s_env', env' =
       cmds
       |> List.fold_left
            (fun (s_env, env) cmd ->
              Transform.check_command debug_flag s_env cmd;
              let s, s_env' = Infer.infer_command debug_flag s_env cmd in
              let res, env' = Eval.eval_command env cmd in
              (match res with
              | Eval.Immediate value ->
                  assert (List.length s = 1);
                  Printf.printf "- : %s = %s\n"
                    (Schema.string_of_schema (List.hd s))
                    (Value.string_of_value value)
              | Eval.Named (names, values) ->
                  iter3
                    (fun name s value ->
                      Printf.printf "val %s: %s = %s\n" name
                        (Schema.string_of_schema s)
                        (Value.string_of_value value))
                    names s values);
              if debug_flag then (
                Printf.printf "schema env = (fv:[%s]) {%s}\n"
                  ((s_env'.fv |> Type.TypeVarSet.elements :> Type.t list)
                  |> List.map Type.string_of |> String.concat ", ")
                  (List.map
                     (fun (k, v) ->
                       Printf.sprintf "\"%s\": %s" k (Schema.string_of_schema v))
                     s_env'.env
                  |> String.concat "; ");
                Printf.printf "env={%s}\n"
                  (List.filter_map
                     (fun (k, v) ->
                       match !v with
                       | Some (Value.VBuiltinFun _) -> None
                       | Some v' ->
                           Some
                             (Printf.sprintf "\"%s\": %s" k
                                (Value.string_of_value v'))
                       | None ->
                           failwith
                             "This is a bug. Please Contact the author to fix \
                              this")
                     env'
                  |> String.concat ";"));
              (s_env', env'))
            (s_env, env)
     in
     read_eval_print s_env' env'
   with
  | Parser.Error -> Printf.printf "Error: Syntax error\n"
  | Transform.DuplicateVariableName name ->
      name
      |> Printf.printf "Variable %s is bound several times in this matching\n"
  | Transform.InvalidLetRecRhs e ->
      Expr.string_of_expr e
      |> Printf.printf
           "Error: This kind of expression is not allowed as right-hand side \
            of `let rec': \n %s\n"
  | Transform.UnboundVariable v ->
      v |> Printf.printf "Error: Unbound value %s\n";
      Printexc.print_backtrace stdout
  | Infer.BadConstraintError (t1, t2) ->
      Printf.printf "Error: Cannot unify %s and %s\n" (Type.string_of t1)
        (Type.string_of t2)
  | Infer.RecursiveOccurenceError (alpha, t) ->
      Printf.printf "Error: Recursive occurence of %s in %s\n"
        (Type.string_of (alpha :> Type.t))
        (Type.string_of t)
  | Value.TypeError s -> Printf.printf "Error: %s\n" s
  | Eval.NotCallable v -> Printf.printf "Error: %s is not callable\n" (Value.string_of_value v)
  | Invalid_argument str -> Printf.printf "Error: %s\n" str
  | Division_by_zero -> Printf.printf "Exception: Division_by_zero\n"
  | Failure s -> s |> Printf.printf "Error: %s\n"
  | e -> raise e);
  read_eval_print s_env env

(* let rec eval_from_str type_env env src=
   print_string "# ";
   flush stdout;
   let cmd = Parser.toplevel Lexer.main (Lexing.from_string src) in
   let id, newenv, v = eval_command env cmd in
   Printf.printf "%s = %s\n" id (string_of_value v);
   read_eval_print newenv *)
(* let _ = record_backtrace true *)
let _ = read_eval_print Value.initial_schema_env Value.initial_env
