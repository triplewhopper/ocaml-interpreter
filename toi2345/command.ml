type 'a t =
  | CExp of 'a
  | CDecls of (string, 'a) Bindings.t
  | CRecDecls of (string, 'a) Bindings.t

type 'a command = 'a t
let string_of_command : 'a command -> string =
  let str_of_decl var e = Printf.sprintf "val %s: %s" var (Expr.string_of_expr e)
  and str_of_rec_decl var e =
    Printf.sprintf "rec val %s: %s" var (Expr.string_of_expr e)
  in
  function
  | CExp e -> Expr.string_of_expr e
  | CDecls (xs, es) -> List.map2 str_of_decl xs es |> String.concat "\n"
  | CRecDecls (xs, fs) ->
      List.map2 str_of_rec_decl xs fs |> String.concat "\n"
