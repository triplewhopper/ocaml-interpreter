type value = Value.value
type thunk = Value.thunk
type expr = Expr.t
type 'a command = 'a Command.command
type ('a, 'b) bindings = ('a, 'b) Bindings.t

exception NotCallable of value
exception NotImplementedError of string

let string_of_env env =
  Printf.sprintf "{%s}"
    (env
    |> List.filter_map (fun (x, v) ->
           match !v with
           | Some (`VBuiltinFun _) | None -> None
           | Some v -> Some (Printf.sprintf "%s=%s" x (Value.string_of_value v)))
    |> String.concat ", ")

let depth = ref 0

let rec eval_thunk (t : thunk) : value =
  depth := !depth + 1;
  let v =
    match t with
    | Value.Thunk (e, env) ->
        let res = eval_expr env e in
        Printf.printf "%*seval_thunk: %s = %s\n" (!depth * 2) ""
          (Value.string_of_thunk t)
          (Value.string_of_value res);
        res
    | Value.BuiltinFunction f -> (f :> value)
  in
  depth := !depth - 1;
  v

and eval_expr (env : thunk option ref Env.t) (e : expr) : value =
  match e with
  | `EConstInt i -> `VInt i
  | `EConstBool b -> `VBool b
  | `EConstUnit -> `VUnit
  | `EVar x -> (
      try
        match !(Env.lookup x env) with
        | Some thunk -> eval_thunk thunk
        | None -> raise (Transform.InvalidLetRecRhs (`EVar x))
      with Not_found -> raise (Transform.UnboundVariable x))
  | `ECall (e1, e2) -> (
      let v1 = eval_expr env e1 in
      match v1 with
      | `VFunc (x, e', oenv) ->
          let r = Value.Thunk (e2, env) |> Option.some |> ref in
          eval_expr (!oenv |> Env.extend x r) e'
      | `VBuiltinFun (_, f) -> f (Thunk (e2, env))
      | v -> raise (NotCallable v))
  | `ETuple es ->
      let vs = List.map (Value.make_thunk env) es in
      `VTuple vs
  | `EList es ->
      let vs = List.map (Value.make_thunk env) es in
      `VList vs
  | `EMatch (_, _) -> raise (NotImplementedError "`EMatch")
  | `EFun (_, var, body) -> `VFunc (var, body, ref env)
  | `ELet ((vars, e1s), e2) ->
      (* let v1s = List.map (eval_expr env) e1s in *)
      let env' =
        List.fold_left2
          (fun env0 var e ->
            let thunk = Value.Thunk (e, env) in
            env0 |> Env.extend var (ref (Some thunk)))
          env vars e1s
      in
      eval_expr env' e2
  | `ELetRec ((vars, es), body) ->
      (* let rec var1=e1 and var2=e2 ... and var_N=e_N in body *)
      let env' =
        List.fold_left
          (fun env0 var -> env0 |> Env.extend var (ref None))
          env vars
      in
      List.iter2
        (fun var rhs ->
          let v = env' |> Env.lookup var in
          assert (Option.is_none !v);
          v := Some (Thunk (rhs, env')))
        vars es;
      eval_expr env' body
  | `EIf (e1, e2, e3) -> (
      let v1 = eval_expr env e1 in
      match v1 with
      | `VBool true -> eval_expr env e2
      | `VBool false -> eval_expr env e3
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
        let v = eval_thunk (Thunk (e, env)) in
        (Immediate (Some v), env)
  | CDecls (names, es) ->
      if Options.inference_only then (
        Printf.eprintf "type inference done.\n";
        flush stderr;
        (Named (names, None), env))
      else
        let vs = List.map (eval_expr env) es in
        (* let vs' = vs |> List.map (fun v -> ref (Some v)) in *)
        let env' =
          env
          |> Env.extends names
               (List.map (fun e -> ref (Some (Value.Thunk (e, env)))) es)
        in
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
            v := Some (Thunk (rhs, env')))
          names es;
        (Named (names, Some vs), env')

open Value

let rec equal : value * value -> _ = function
  | (`VFunc _ | `VBuiltinFun _), (`VFunc _ | `VBuiltinFun _) ->
      raise (Invalid_argument "compare: functional value")
  | `VInt x, `VInt y -> `VBool (x = y)
  | `VBool x, `VBool y -> `VBool (x = y)
  | `VUnit, `VUnit -> `VBool true
  | `VTuple xs, `VTuple ys | `VList xs, `VList ys ->
      `VBool
        (List.length xs = List.length ys
        && List.for_all2
             (fun x y -> equal (eval_thunk x, eval_thunk y) = `VBool true)
             xs ys)
  | `VCons (x, xs), `VCons (y, ys) ->
      `VBool
        (equal (eval_thunk x, eval_thunk y) = `VBool true
        && equal (eval_thunk xs, eval_thunk ys) = `VBool true)
  | `VCons _, `VList [] | `VList [], `VCons _ -> `VBool false
  | `VCons (x, xs), `VList ys | `VList ys, `VCons (x, xs) ->
      `VBool
        (equal (eval_thunk x, eval_thunk (List.hd ys)) = `VBool true
        && equal (eval_thunk xs, `VList (List.tl ys)) = `VBool true)
  | x, y -> raise (TypeError (string_of_value x ^ " = " ^ string_of_value y))

let builtins =
  let open Value in
  let wrapper (op : string) f =
    (op, `VBuiltinFun (op, fun thunk -> f (eval_thunk thunk)))
  in
  let wrapper2 op f =
    ( op,
      `VBuiltinFun
        ( op,
          fun x ->
            `VBuiltinFun (op ^ "'", fun y -> f (eval_thunk x, eval_thunk y)) )
    )
  in
  let wrapper2_lazy op f =
    (op, `VBuiltinFun (op, fun x -> `VBuiltinFun (op ^ "'", fun y -> f (x, y))))
  in
  let sv = string_of_value and st = string_of_thunk in
  [
    wrapper2 "=" equal;
    wrapper2 "+" (function
      | `VInt x', `VInt y' -> `VInt (x' + y')
      | x, y -> raise (TypeError (sv x ^ " + " ^ sv y)));
    wrapper2 "-" (function
      | `VInt x', `VInt y' -> `VInt (x' - y')
      | x, y -> raise (TypeError (sv x ^ " - " ^ sv y)));
    wrapper2 "*" (function
      | `VInt x', `VInt y' -> `VInt (x' * y')
      | x, y -> raise (TypeError (sv x ^ " * " ^ sv y)));
    wrapper2 "/" (function
      | `VInt x', `VInt y' -> `VInt (x' / y')
      | x, y -> raise (TypeError (sv x ^ " / " ^ sv y)));
    wrapper2 "mod" (function
      | `VInt x', `VInt y' -> `VInt (x' mod y')
      | x, y -> raise (TypeError (sv x ^ " mod " ^ sv y)));
    wrapper2 ">" (function
      | `VInt x', `VInt y' -> `VBool (x' > y')
      | x, y -> raise (TypeError (sv x ^ " > " ^ sv y)));
    wrapper2 "<" (function
      | `VInt x', `VInt y' -> `VBool (x' < y')
      | x, y -> raise (TypeError (sv x ^ " < " ^ sv y)));
    wrapper2 ">=" (function
      | `VInt x', `VInt y' -> `VBool (x' >= y')
      | x, y -> raise (TypeError (sv x ^ " >= " ^ sv y)));
    wrapper2 "<=" (function
      | `VInt x', `VInt y' -> `VBool (x' <= y')
      | x, y -> raise (TypeError (sv x ^ " <= " ^ sv y)));
    wrapper2_lazy "&&" (fun (thunk1, thunk2) ->
        match eval_thunk thunk1 with
        | `VBool true -> eval_thunk thunk2
        | `VBool false -> `VBool false
        | x -> raise (TypeError (sv x ^ " && " ^ st thunk2)));
    wrapper2_lazy "||" (fun (thunk1, thunk2) ->
        match eval_thunk thunk1 with
        | `VBool true -> `VBool true
        | `VBool false -> eval_thunk thunk2
        | x -> raise (TypeError (sv x ^ " || " ^ st thunk2)));
    wrapper "fst" (function
      | `VTuple [ x'; _ ] -> eval_thunk x'
      | x -> raise (TypeError ("fst " ^ sv x)));
    wrapper "snd" (function
      | `VTuple [ _; y' ] -> eval_thunk y'
      | x -> raise (TypeError ("snd " ^ sv x)));
    wrapper2_lazy "::" (function x, y -> `VCons (x, y));
    wrapper "hd" (function
      | `VCons (x', _) -> eval_thunk x'
      | `VList (x' :: _) -> eval_thunk x'
      | `VList [] -> raise (Invalid_argument "hd []")
      | x -> raise (TypeError ("hd " ^ sv x)));
    wrapper "tl" (function
      | `VCons (_, xs) -> eval_thunk xs
      | `VList (_ :: xs) -> `VList xs
      | `VList [] -> raise (Invalid_argument "tl []")
      | x -> raise (TypeError ("tl " ^ sv x)));
    wrapper "~-" (function
      | `VInt x' -> `VInt (-x')
      | x -> raise (TypeError ("-" ^ sv x)));
    wrapper "~+" (function
      | `VInt _ as x -> x
      | x -> raise (TypeError ("+" ^ sv x)));
    wrapper "print_int" (function
      | `VInt x' ->
          print_int x';
          `VUnit
      | x -> raise (TypeError ("print_int " ^ sv x)));
    wrapper "print_bool" (function
      | `VBool x' ->
          print_string (string_of_bool x');
          `VUnit
      | x -> raise (TypeError ("print_bool " ^ sv x)));
    wrapper "print_newline" (function
      | `VUnit ->
          print_newline ();
          `VUnit
      | x -> raise (TypeError ("print_newline " ^ sv x)));
  ]

let initial_env =
  let open Env in
  let ks, vs = List.split builtins in
  empty |> extends ks (List.map (fun v -> ref (Some (BuiltinFunction v))) vs)

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
  let hd, tl =
    let alpha = Type.new_typevar () in
    ( wrapper [ alpha ] (Type.ty_list (alpha :> Type.t)) (alpha :> Type.t),
      wrapper [ alpha ]
        (Type.ty_list (alpha :> Type.t))
        (Type.ty_list (alpha :> Type.t)) )
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
  |> SchemaEnv.extend "hd" hd |> SchemaEnv.extend "tl" tl
  |> SchemaEnv.extend "print_int" (wrapper [] Type.ty_int Type.ty_unit)
  |> SchemaEnv.extend "print_bool" (wrapper [] Type.ty_bool Type.ty_unit)
  |> SchemaEnv.extend "print_newline" (wrapper [] Type.ty_unit Type.ty_unit)
