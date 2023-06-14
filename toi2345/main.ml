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

let print_results results =
  results
  |> List.iter (function
       | s, Eval.Immediate (Some value) ->
           assert (List.length s = 1);
           Printf.printf "- : %s = %s\n"
             (Schema.string_of_schema (List.hd s))
             (Value.string_of_value value)
       | s, Eval.Immediate None ->
           assert (List.length s = 1);
           Printf.printf "- : %s\n" (Schema.string_of_schema (List.hd s))
       | s, Eval.Named (names, Some values) ->
           iter3
             (fun name s value ->
               Printf.printf "val %s: %s = %s\n" name
                 (Schema.string_of_schema s)
                 (Value.string_of_value value))
             names s values
       | s, Eval.Named (names, None) ->
           List.iter2
             (fun name s ->
               Printf.printf "val %s: %s\n" name (Schema.string_of_schema s))
             names s)

let read_eval_print (s_env : Infer.SchemaEnv.t) env =
  if Options.inference_only then (Printf.eprintf "Inference only mode\n"; flush stderr);
  let s_env = ref s_env and env = ref env and eof_flag = ref false in
  while not !eof_flag do
    print_string "# ";
    flush stdout;
    try
      let cmds = Parser.toplevel Lexer.main (Lexing.from_channel stdin) in
      let results = ref [] in
      let s_env', env' =
        cmds
        |> List.fold_left
             (fun (s_env, env) (cmd : Expr.t0 Command.t) ->
               Transform.check_command s_env cmd;
               let cmd : Expr.t Command.t =
                 Transform.transform_command s_env cmd
               in
               let s, s_env' = Infer.infer_command s_env cmd in
               let res, env' = Eval.eval_command env cmd in
               results := (s, res) :: !results;
               if Options.debug_flag then (
                 print_results [ (s, res) ];
                 Printf.printf "schema env = %s\n"
                   (Schema.string_of_senv s_env');
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
             (!s_env, !env)
      in
      if not Options.debug_flag then (
        print_results (List.rev !results);
        flush stdout);
      s_env := s_env';
      env := env'
    with
    | Parser.Error -> Printf.printf "Error: Syntax error\n"
    | Transform.DuplicateVariableName name ->
        name
        |> Printf.printf "Variable %s is bound several times in this matching\n"
    | Transform.InvalidLetRecRhs e ->
        Expr.string_of_expr e
        |> Printf.printf
             "Error: This kind of expression is not allowed as right-hand side \
              of `let rec': \n\
             \ %s\n"
    | Transform.UnboundVariable v ->
        v |> Printf.printf "Error: Unbound value %s\n"
    | Infer.BadConstraintError (t1, t2) ->
        Printf.printf "Error: Cannot unify %s and %s\n" (Type.string_of t1)
          (Type.string_of t2)
    | Infer.RecursiveOccurenceError (alpha, t) ->
        Printf.printf "Error: Recursive occurence of %s in %s\n"
          (Type.string_of (alpha :> Type.t))
          (Type.string_of t)
    | Value.TypeError s -> Printf.printf "Error: %s\n" s
    | Eval.NotCallable v ->
        Printf.printf "Error: %s is not callable\n" (Value.string_of_value v)
    | Invalid_argument str -> Printf.printf "Error: %s\n" str
    | Division_by_zero -> Printf.printf "Exception: Division_by_zero\n"
    | Failure s -> s |> Printf.printf "Error: %s\n"
    | Lexer.Eof -> eof_flag := true
    | e -> raise e
  done

(* let rec eval_from_str type_env env src=
   print_string "# ";
   flush stdout;
   let cmd = Parser.toplevel Lexer.main (Lexing.from_string src) in
   let id, newenv, v = eval_command env cmd in
   Printf.printf "%s = %s\n" id (string_of_value v);
   read_eval_print newenv *)
(* let _ = record_backtrace true *)
let () = read_eval_print Value.initial_schema_env Value.initial_env
