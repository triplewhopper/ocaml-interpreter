type t =
  [ `EConstInt of int
  | `EConstBool of bool
  | `EConstUnit
  | `EVar of string
  | `EIf of t * t * t
  | `EBinaryOp of string * t * t
  | `EUnaryOp of string * t
  | `ECall of t * t
  | `EFun of int * string * t (* #id var body *)
  | `EDFun of int * string * t (* #id var body *)
  | `ELet of (string, t) Bindings.t * t (* let var = e1 in e2 *)
  | `ELetRec of
    (string, t) Bindings.t * t (* let rec var = (e1: 'a->'b) in e2 *) ]

let rec string_of_expr (e : t) =
  let f = string_of_expr in
  match e with
  | `EConstInt i -> Printf.sprintf "(`EConstInt %d)" i
  | `EConstBool b -> Printf.sprintf "(`EConstBool %b)" b
  | `EConstUnit -> "`EConstUnit"
  | `EVar x -> Printf.sprintf "(`EVar \"%s\")" x
  | `EBinaryOp (op, e1, e2) ->
      let s1, s2 = (f e1, f e2) in
      Printf.sprintf "`EBinaryOp (\"%s\", %s, %s)" op s1 s2
  | `EUnaryOp (op, e) ->
      let s = f e in
      Printf.sprintf "`EUnaryOp (\"%s\", %s)" op s
  | `EIf (e1, e2, e3) ->
      let s1, s2, s3 = (f e1, f e2, f e3) in
      Printf.sprintf "`EIf (%s, %s, %s)" s1 s2 s3
  | `ECall (e1, e2) ->
      let s1, s2 = (f e1, f e2) in
      Printf.sprintf "`ECall (%s, %s)" s1 s2
  | `EFun (id, var, e) -> Printf.sprintf "`EFun(%d, \"%s\", %s)" id var (f e)
  | `EDFun (id, var, e) -> Printf.sprintf "`EDFun(%d, \"%s\", %s)" id var (f e)
  | `ELet ((xs, es), e2) ->
      let sxs =
        xs |> List.map (Printf.sprintf "\"%s\"") |> String.concat "; "
      in
      let ses = List.map string_of_expr es |> String.concat "; " in

      Printf.sprintf "`ELet(([%s], [%s]), %s)" sxs ses (f e2)
  | `ELetRec ((xs, es), e2) ->
      let sxs =
        xs |> List.map (Printf.sprintf "\"%s\"") |> String.concat "; "
      in
      let ses = List.map string_of_expr es |> String.concat "; " in

      Printf.sprintf "`ELetRec(([%s], [%s]), %s)" sxs ses (f e2)

module StringSet = Set.Make (String)

let free_vars e =
  let rec free_vars' e' =
    match e' with
    | `EConstInt _ | `EConstBool _ | `EConstUnit -> StringSet.empty
    | `EVar x -> StringSet.singleton x
    | `EBinaryOp (_, e1, e2) | `ECall (e1, e2) ->
        StringSet.union (free_vars' e1) (free_vars' e2)
    | `EUnaryOp (_, e1) -> free_vars' e1
    | `EIf (e1, e2, e3) ->
        free_vars' e1
        |> StringSet.union (free_vars' e2)
        |> StringSet.union (free_vars' e3)
    | `EFun (_, x, e1) -> StringSet.remove x (free_vars' e1)
    | `EDFun (_, x, e1) ->
        if e == e' then StringSet.remove x (free_vars' e1) else StringSet.empty
    | `ELet ((xs, es), e2) ->
        es |> List.map free_vars'
        |> List.fold_left StringSet.union StringSet.empty
        |> StringSet.union
             (StringSet.diff (free_vars' e2) (StringSet.of_list xs))
    | `ELetRec ((xs, es), e2) ->
        StringSet.diff (StringSet.of_list xs)
          (es |> List.map free_vars'
          |> List.fold_left StringSet.union StringSet.empty
          |> StringSet.union (free_vars' e2))
  in

  free_vars' e
