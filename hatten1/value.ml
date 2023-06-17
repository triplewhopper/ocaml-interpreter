type value =
  VInt of int
  | VBool of bool
  | VUnit
  | VTuple of dval list
  | VList of dval list
  | VCons of dval * dval
  | VFunc of string * Expr.t * dval option ref Env.t
  | VBuiltinFun of string * (dval -> value) 

and dval = DThunk of Expr.t * dval option ref Env.t | DVal of value



(* let resolve (type a) : a promise -> resolved promise = function
  | Pending (a, f) -> Resolved (f a)
  | Resolved a -> Resolved a *)
let make_thunk env e = DThunk (e, env)
let make_dval v = DVal v

let rec string_of_dval = function
  | DThunk (e, _) -> "<DThunk " ^ Expr.string_of_expr e ^ ">"
  | DVal v -> string_of_value v
  (* | BuiltinFunction (`VBuiltinFun (name, _)) ->
      Printf.sprintf "<built-in %s>" name *)



and string_of_value (v : value) : string =
  match v with
  | VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VUnit -> "()"
  | VCons (x, xs) -> string_of_dval x ^ " :: " ^ string_of_dval xs
  | VList xs ->
      "[" ^ (xs |> List.map string_of_dval |> String.concat "; ") ^ "]"
  | VTuple vs ->
      "(" ^ (vs |> List.map string_of_dval |> String.concat ", ") ^ ")"
  | VFunc (var, _, _) -> Printf.sprintf "<fun (%s)>" var
  | VBuiltinFun (name, _) -> Printf.sprintf "<built-in %s>" name

exception TypeError of string
