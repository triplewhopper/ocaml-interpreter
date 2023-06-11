type value =
  | VInt of int
  | VBool of bool
  | VUnit
  | VTuple of value list 
  | VFunc of string * Expr.t * value option ref Env.t ref
  (* | VRecFun of string * [ `EFun of int * string * expr ] * value Env.t *)
  | VBuiltinFun of string * (value -> value)
 (* | VDFun of string * Expr.t  (** value option ref Env.t ref *) *)

let rec string_of_value (v : value) : string =
  match v with
  | VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VUnit -> "()"
  | VTuple vs ->
      "("
      ^ (vs |> List.map string_of_value |> String.concat ", ")
      ^ ")"
  | VFunc (var, _, _) -> Printf.sprintf "<fun (%s)>" var
  | VBuiltinFun (name, _) -> Printf.sprintf "<built-in %s>" name
  (* | VDFun (name, body) ->
      Printf.sprintf "<dfun %s, [%s]>" name
        (Expr.free_vars body |> Expr.StringSet.remove name
       |> Expr.StringSet.elements |> String.concat ", ") *)

exception TypeError of string
let rec equal = function
  | (VFunc _ | (*VDFun _ |*) VBuiltinFun _), (VFunc _ | (*VDFun _ |*) VBuiltinFun _) ->
      raise (Invalid_argument "compare: functional value")
  | VInt x, VInt y -> VBool (x = y)
  | VBool x, VBool y -> VBool (x = y)
  | VUnit, VUnit -> VBool true
  | VTuple xs, VTuple ys ->
      VBool
        (List.length xs = List.length ys
        && List.for_all2 (fun x y -> equal (x, y) = VBool true) xs ys)
  | x, y -> raise (TypeError ((string_of_value x) ^ " = " ^ (string_of_value y)))



let builtins =
  let wrapper op f = (op, VBuiltinFun (op, f)) in
  let wrapper2 op f =
    (op, VBuiltinFun (op, fun x -> VBuiltinFun (op ^ "'", fun y -> f (x, y))))
  in
  let sv = string_of_value in
  [
    wrapper2 "=" equal;
    wrapper2 "+" (function
      | VInt x', VInt y' -> VInt (x' + y')
      | x, y -> raise (TypeError (sv x ^ " + " ^ sv y)));
    wrapper2 "-" (function
      | VInt x', VInt y' -> VInt (x' - y')
      | x, y -> raise (TypeError (sv x ^ " - " ^ sv y)));
    wrapper2 "*" (function
      | VInt x', VInt y' -> VInt (x' * y')
      | x, y -> raise (TypeError (sv x ^ " * " ^ sv y)));
    wrapper2 "/" (function
      | VInt x', VInt y' -> VInt (x' / y')
      | x, y -> raise (TypeError (sv x ^ " / " ^ sv y)));
    wrapper2 "mod" (function
      | VInt x', VInt y' -> VInt (x' mod y')
      | x, y -> raise (TypeError (sv x ^ " mod " ^ sv y)));
    wrapper2 ">" (function
      | VInt x', VInt y' -> VBool (x' > y')
      | x, y -> raise (TypeError (sv x ^ " > " ^ sv y)));
    wrapper2 "<" (function
      | VInt x', VInt y' -> VBool (x' < y')
      | x, y -> raise (TypeError (sv x ^ " < " ^ sv y)));
    wrapper2 ">=" (function
      | VInt x', VInt y' -> VBool (x' >= y')
      | x, y -> raise (TypeError (sv x ^ " >= " ^ sv y)));
    wrapper2 "<=" (function
      | VInt x', VInt y' -> VBool (x' <= y')
      | x, y -> raise (TypeError (sv x ^ " <= " ^ sv y)));
    wrapper2 "&&" (function
      | VBool x', VBool y' -> VBool (x' && y')
      | x, y -> raise (TypeError (sv x ^ " && " ^ sv y)));
    wrapper2 "||" (function
      | VBool x', VBool y' -> VBool (x' || y')
      | x, y -> raise (TypeError (sv x ^ " || " ^ sv y)));
    wrapper "~-" (function
      | VInt x' -> VInt (-x')
      | x -> raise (TypeError ("-" ^ sv x)));
    wrapper "~+" (function
      | VInt _ as x -> x
      | x -> raise (TypeError ("+" ^ sv x)));
    wrapper "print_int" (function
      | VInt x' ->
          print_int x';
          VUnit
      | x -> raise (TypeError ("print_int " ^ sv x)));
    wrapper "print_bool" (function
      | VBool x' ->
          print_string (string_of_bool x');
          VUnit
      | x -> raise (TypeError ("print_bool " ^ sv x)));
    wrapper "print_newline" (function
      | VUnit ->
          print_newline ();
          VUnit
      | x -> raise (TypeError ("print_newline " ^ sv x)));
  ]

let initial_env =
  let open Env in
  let ks, vs = List.split builtins in
  empty |> extends ks (List.map (fun v -> ref (Some v)) vs)

let initial_schema_env =
  let open Schema in
  let iii =
    schema TypeVarSet.empty (Type.func (`Int, Type.func (`Int, `Int)))
  in
  let iib =
    schema TypeVarSet.empty (Type.func (`Int, Type.func (`Int, `Bool)))
  in
  let bbb =
    schema TypeVarSet.empty (Type.func (`Bool, Type.func (`Bool, `Bool)))
  in
  let alpha = Type.new_typevar () in
  let aab =
    schema
      (TypeVarSet.singleton alpha)
      (Type.func ((alpha :> Type.t), Type.func ((alpha :> Type.t), `Bool)))
  in
  SchemaEnv.empty |> SchemaEnv.extend "+" iii |> SchemaEnv.extend "-" iii
  |> SchemaEnv.extend "*" iii |> SchemaEnv.extend "/" iii
  |> SchemaEnv.extend "mod" iii |> SchemaEnv.extend ">" iib
  |> SchemaEnv.extend "<" iib |> SchemaEnv.extend ">=" iib
  |> SchemaEnv.extend "<=" iib |> SchemaEnv.extend "&&" bbb
  |> SchemaEnv.extend "||" bbb
  |> SchemaEnv.extend "~-" (schema TypeVarSet.empty (Type.func (`Int, `Int)))
  |> SchemaEnv.extend "~+" (schema TypeVarSet.empty (Type.func (`Int, `Int)))
  |> SchemaEnv.extend "=" aab
  |> SchemaEnv.extend "print_int"
       (schema TypeVarSet.empty (Type.func (`Int, `Unit)))
  |> SchemaEnv.extend "print_bool"
       (schema TypeVarSet.empty (Type.func (`Bool, `Unit)))
  |> SchemaEnv.extend "print_newline"
       (schema TypeVarSet.empty (Type.func (`Unit, `Unit)))
