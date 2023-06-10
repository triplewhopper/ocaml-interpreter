type t =
  | CExp of Expr.t
  (* | CDecl of string * expr *)
  | CDecls of (string, Expr.t) Bindings.t
  (* | CRecDecl of string * string * expr *)
  | CRecDecls of (string, Expr.t) Bindings.t

type command = t
let string_of_command : command -> string =
  let str_of_decl var e = Printf.sprintf "val %s: %s" var (Expr.string_of_expr e)
  and str_of_rec_decl var e =
    Printf.sprintf "rec val %s: %s" var (Expr.string_of_expr e)
  in
  function
  | CExp e -> Expr.string_of_expr e
  | CDecls (xs, es) -> List.map2 str_of_decl xs es |> String.concat "\n"
  | CRecDecls (xs, fs) ->
      List.map2 str_of_rec_decl xs fs |> String.concat "\n"
