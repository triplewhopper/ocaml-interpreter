type value =
  [ `VInt of int
  | `VBool of bool
  | `VUnit
  | `VTuple of thunk list
  | `VList of thunk list
  | `VCons of thunk * thunk
  | `VFunc of string * Expr.t * thunk option ref Env.t
  | `VBuiltinFun of string * (thunk -> value) ]

and thunk =
  | Thunk of Expr.t * thunk option ref Env.t
  | BuiltinFunction of [ `VBuiltinFun of string * (thunk -> value) ]


let string_of_thunk = function
  | Thunk (e, _) -> "<thunk " ^ Expr.string_of_expr e ^ ">"
  | BuiltinFunction (`VBuiltinFun (name, _)) ->
      Printf.sprintf "<built-in %s>" name

let make_thunk env e = Thunk (e, env)

let string_of_value (v : value) : string =
  match v with
  | `VInt i -> string_of_int i
  | `VBool b -> string_of_bool b
  | `VUnit -> "()"
  | `VCons (x, xs) -> string_of_thunk x ^ " :: " ^ string_of_thunk xs
  | `VList xs ->
      "[" ^ (xs |> List.map string_of_thunk |> String.concat "; ") ^ "]"
  | `VTuple vs ->
      "(" ^ (vs |> List.map string_of_thunk |> String.concat ", ") ^ ")"
  | `VFunc (var, _, _) -> Printf.sprintf "<fun (%s)>" var
  | `VBuiltinFun (name, _) -> Printf.sprintf "<built-in %s>" name

exception TypeError of string
