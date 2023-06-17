type pattern = Pattern.pattern

type t0 =
  [ `EConstInt of int
  | `EConstBool of bool
  | `EConstUnit
  | `EVar of string
  | `EIf of t0 * t0 * t0
  | `EBinaryOp of string * t0 * t0
  | `EUnaryOp of string * t0
  | `ECall of t0 * t0
  | `ETuple of t0 list
  | `EList of t0 list
  | `EMatch of t0 * (pattern * t0) list
  | `EFun of int * string * t0 (* #id var body *)
  | `ELet of (string, t0) Bindings.t * t0 (* let var = e1 in e2 *)
  | `ELetRec of
    (string, t0) Bindings.t * t0 (* let rec var = (e1: 'a->'b) in e2 *) ]
type equation = pattern * t
and t =
  [ `EConstInt of int
  | `EConstBool of bool
  | `EConstUnit
  | `EVar of string
  | `EIf of t * t * t
  | `ECall of t * t
  | `ETuple of t list
  | `EList of t list
  | `EMatch of t * equation list
  | `EFun of int * string * t (* #id var body *)
  | `ELet of (string, t) Bindings.t * t (* let var = e1 in e2 *)
  | `ELetRec of
    (string, t) Bindings.t * t (* let rec var = (e1: 'a->'b) in e2 *) ]
let remove_parentheses s =
  let len = String.length s in
  if len >= 2 && s.[0] = '(' && s.[len - 1] = ')' then
    String.sub s 1 (len - 2)
  else s

let string_of_expr e =
    let rec string_of_expr' e =
  let f = string_of_expr' in
  match e with
  | `EConstInt i -> Printf.sprintf "%d" i
  | `EConstBool b -> Printf.sprintf "%b" b
  | `EConstUnit -> "()"
  | `EVar "::" -> "(::)"
  | `EVar "+" -> "(+)"
  | `EVar "-" -> "(-)"
  | `EVar "*" -> "( * )"
  | `EVar "/" -> "(/)"
  | `EVar "mod" -> "(mod)"
  | `EVar x -> x
  | `EBinaryOp (op, e1, e2) ->
      let s1, s2 = (f e1, f e2) in
      Printf.sprintf "(%s %s %s)" s1 op s2
  | `EUnaryOp (op, e) ->
      let s = f e in
      Printf.sprintf "(%s %s)" op s
  | `EIf (e1, e2, e3) ->
      let s1, s2, s3 = (f e1, f e2, f e3) in
      Printf.sprintf "(if %s then %s else %s)" s1 s2 s3
  | `ECall (e1, e2) ->
      let s1, s2 = (f e1, f e2) in
      let s1 = (match e1 with `ECall _ -> remove_parentheses s1 | _ -> s1) in
      Printf.sprintf "(%s %s)" s1 s2
  | `ETuple es -> Printf.sprintf "(%s)" (List.map f es |> String.concat ", ")
  | `EList es -> Printf.sprintf "[%s]" (List.map f es |> String.concat "; ")
  | `EMatch (e, qs) ->
      let sqs =
        qs
        |> List.map (fun (p, e) ->
               Printf.sprintf "%s -> %s" (Pattern.string_of_pattern p) (f e))
        |> String.concat " | "
      in
      Printf.sprintf "(match %s with %s)" (f e) sqs
  | `EFun (id, var, e) -> 
    let s = f e in 
    let s = (match e with `EFun _ | `ECall _ -> remove_parentheses s | _ -> s) in
    Printf.sprintf "(fun#%d %s -> %s)" id var s
  (* | `EDFun (id, var, e) -> Printf.sprintf "`EDFun(%d, \"%s\", %s)" id var (f e) *)
  | `ELet ((xs, es), e2) ->
      let sxs =
        xs |> List.map (Printf.sprintf "\"%s\"") |> String.concat ", "
      in
      let ses = List.map f es |> String.concat ", " in
      let ses = if List.length es = 1 then ses else "(" ^ ses ^ ")" in
      Printf.sprintf "(let %s = %s in %s)" sxs ses (f e2)
  | `ELetRec ((xs, es), e2) ->
      let sxs =
        xs |> List.map (Printf.sprintf "\"%s\"") |> String.concat ", "
      in
      let ses = List.map f es |> String.concat ", " in
      let ses = if List.length es = 1 then ses else "(" ^ ses ^ ")" in
      Printf.sprintf "(let rec %s = %s in %s)" sxs ses (f e2)
    in
    string_of_expr' e |> remove_parentheses
