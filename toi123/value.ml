type value =
  | VInt of int
  | VBool of bool
  | VUnit
  | VList of value list
  | VTuple of value list
  | VFunc of string * Expr.t * value option ref Env.t ref
  | VBuiltinFun of string * (value -> value)

let rec string_of_value (v : value) : string =
  match v with
  | VInt i -> string_of_int i
  | VBool b -> string_of_bool b
  | VUnit -> "()"
  | VList xs ->
      "[" ^ (xs |> List.map string_of_value |> String.concat "; ") ^ "]"
  | VTuple vs ->
      "(" ^ (vs |> List.map string_of_value |> String.concat ", ") ^ ")"
  | VFunc (var, _, _) -> Printf.sprintf "<fun (%s)>" var
  | VBuiltinFun (name, _) -> Printf.sprintf "<built-in %s>" name

exception TypeError of string

let rec equal = function
  | (VFunc _ | VBuiltinFun _), (VFunc _ | VBuiltinFun _) ->
      raise (Invalid_argument "compare: functional value")
  | VInt x, VInt y -> VBool (x = y)
  | VBool x, VBool y -> VBool (x = y)
  | VUnit, VUnit -> VBool true
  | VList xs, VList ys ->
      VBool
        (List.length xs = List.length ys
        && List.for_all2 (fun x y -> equal (x, y) = VBool true) xs ys)
  | VTuple xs, VTuple ys ->
      VBool
        (List.length xs = List.length ys
        && List.for_all2 (fun x y -> equal (x, y) = VBool true) xs ys)
  | x, y -> raise (TypeError (string_of_value x ^ " = " ^ string_of_value y))

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
    wrapper "fst" (function
      | VTuple [ x'; _ ] -> x'
      | x -> raise (TypeError ("fst " ^ sv x)));
    wrapper "snd" (function
      | VTuple [ _; y' ] -> y'
      | x -> raise (TypeError ("snd " ^ sv x)));
    wrapper2 "::" (function
      | x, VList xs -> VList (x :: xs)
      | x, y -> raise (TypeError (sv x ^ " :: " ^ sv y)));
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
  let wrapper2 vars x y z =
    schema (TypeVarSet.of_list vars)
      (Type.func ((x :> Type.t), Type.func ((y :> Type.t), (z :> Type.t))))
  in
  let wrapper vars x y =
    schema (TypeVarSet.of_list vars) (Type.func ((x :> Type.t), (y :> Type.t)))
  in
  let iii = wrapper2 [] Type.ty_int Type.ty_int Type.ty_int in
  let iib = wrapper2 [] Type.ty_int Type.ty_int Type.ty_bool in
  let bbb = wrapper2 [] Type.ty_bool Type.ty_bool Type.ty_bool in
  let aa_bool =
    let alpha = Type.new_typevar () in
    wrapper2 [ alpha ] (alpha :> Type.t) (alpha :> Type.t) Type.ty_bool
  in
  let fst =
    let alpha = Type.new_typevar () in
    let beta = Type.new_typevar () in
    wrapper [ alpha; beta ] (Type.tuple ([ alpha; beta ] :> Type.t list)) alpha
  in
  let snd =
    let alpha = Type.new_typevar () in
    let beta = Type.new_typevar () in
    wrapper [ alpha; beta ] (Type.tuple ([ alpha; beta ] :> Type.t list)) beta
  in
  let cons =
    let alpha = Type.new_typevar () in
    let ty_list = Type.ty_list (alpha :> Type.t) in
    wrapper2 [ alpha ] alpha ty_list ty_list
  in
  SchemaEnv.empty |> SchemaEnv.extend "+" iii |> SchemaEnv.extend "-" iii
  |> SchemaEnv.extend "*" iii |> SchemaEnv.extend "/" iii
  |> SchemaEnv.extend "mod" iii |> SchemaEnv.extend ">" iib
  |> SchemaEnv.extend "<" iib |> SchemaEnv.extend ">=" iib
  |> SchemaEnv.extend "<=" iib |> SchemaEnv.extend "&&" bbb
  |> SchemaEnv.extend "||" bbb |> SchemaEnv.extend "::" cons
  |> SchemaEnv.extend "~-" (wrapper [] Type.ty_int Type.ty_int)
  |> SchemaEnv.extend "~+" (wrapper [] Type.ty_int Type.ty_int)
  |> SchemaEnv.extend "=" aa_bool
  |> SchemaEnv.extend "fst" fst |> SchemaEnv.extend "snd" snd
  |> SchemaEnv.extend "print_int" (wrapper [] Type.ty_int Type.ty_unit)
  |> SchemaEnv.extend "print_bool" (wrapper [] Type.ty_bool Type.ty_unit)
  |> SchemaEnv.extend "print_newline" (wrapper [] Type.ty_unit Type.ty_unit)
