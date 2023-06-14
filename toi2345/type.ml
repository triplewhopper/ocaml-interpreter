type typevar_t = [ `TypeVar of int ]

module TypeVarSet = Set.Make (struct
  type t = typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)

type t_ = t

and t =
  [ `Int
  | `Bool
  | `Unit
  | `Func of int * t * t
  | `Tuple of int * t list
  | `TypeVar of int ]

let is_typevar = function `TypeVar _ -> true | _ -> false
let is_func = function `Func _ -> true | _ -> false
let is_tuple = function `Tuple _ -> true | _ -> false
let is_func_or_tuple = function `Func _ | `Tuple _ -> true | _ -> false

let equal a b =
  match (a, b) with
  | `Int, `Int -> true
  | `Bool, `Bool -> true
  | `Unit, `Unit -> true
  | `TypeVar i, `TypeVar j -> i = j
  | `Tuple (i, _), `Tuple (j, _) -> i = j
  | `Func (i, _, _), `Func (j, _, _) -> i = j
  | _ -> false

let hash t =
  match t with
  | `Int -> -3
  | `Bool -> -2
  | `Unit -> -1
  | `TypeVar i -> 3 * i
  | `Tuple (i, _) -> (3 * i) + 1
  | `Func (i, _, _) -> (3 * i) + 2

module TypeHashtbl = Hashtbl.Make (struct
  type t = t_

  let equal : t -> t -> bool = equal
  let hash : t -> int = hash
end)

module TypeListHashtbl = Hashtbl.Make (struct
  type t = t_ list

  let equal : t -> t -> bool = List.for_all2 equal
  let hash (x : t) = x |> List.map hash |> Hashtbl.hash
end)

let memo table f t =
  match TypeHashtbl.find_opt table t with
  | Some v -> v
  | None ->
      let v = f t in
      TypeHashtbl.add table t v;
      v

let compressed_string_of typ =
  let table = TypeHashtbl.create 0 in
  let rec s' (typ : t) =
    match typ with
    | `Int -> "int"
    | `Bool -> "bool"
    | `Unit -> "unit"
    | `TypeVar i -> Printf.sprintf "'%d" i
    | `Tuple (id, ts) ->
        if TypeHashtbl.mem table typ then Printf.sprintf "<%d>" id
        else (
          TypeHashtbl.add table typ ();
          let ts' =
            List.map
              (fun t ->
                if (not (TypeHashtbl.mem table t)) && is_func_or_tuple t then
                  "(" ^ s' t ^ ")"
                else s' t)
              ts
            |> String.concat " * "
          in
          Printf.sprintf "%s as %d" ts' id)
    | `Func (id, a, b) ->
        if TypeHashtbl.mem table typ then Printf.sprintf "<%d>" id
        else (
          TypeHashtbl.add table typ ();
          if (not (TypeHashtbl.mem table a)) && is_func a then
            Printf.sprintf "(%s) -> %s as %d" (s' a) (s' b) id
          else Printf.sprintf "%s -> %s as %d" (s' a) (s' b) id)
  in
  s' typ

let rec string_of typ : string =
  if Options.compress_type then compressed_string_of typ
  else
    match typ with
    | `Int -> "int"
    | `Bool -> "bool"
    | `Unit -> "unit"
    | `TypeVar i -> Printf.sprintf "'%d" i
    | `Tuple (_, ts) ->
        List.map
          (fun t ->
            let s = string_of t in
            match t with `Func _ | `Tuple _ -> "(" ^ s ^ ")" | _ -> s)
          ts
        |> String.concat " * "
    | `Func (_, (`Func _ as a), b) ->
        Printf.sprintf "(%s) -> %s" (string_of a) (string_of b)
    | `Func (_, a, b) -> Printf.sprintf "%s -> %s" (string_of a) (string_of b)

let fv =
  let table = TypeHashtbl.create 0 in
  let rec fv' typ = memo table fv'' typ
  and fv'' typ =
    match typ with
    | #typevar_t as a -> TypeVarSet.singleton a
    | `Unit | `Int | `Bool -> TypeVarSet.empty
    | `Tuple (_, ts) ->
        List.map fv' ts |> List.fold_left TypeVarSet.union TypeVarSet.empty
    | `Func (_, a, b) -> TypeVarSet.union (fv' a) (fv' b)
  in
  fv'

let func =
  let funcs : t TypeHashtbl.t TypeHashtbl.t = TypeHashtbl.create 100 in
  let n_funcs = ref 0 in
  fun ((a : t), (b : t)) ->
    match TypeHashtbl.find_opt funcs a with
    | Some v -> (
        match TypeHashtbl.find_opt v b with
        | Some i -> i
        | None ->
            n_funcs := !n_funcs + 1;
            let res = `Func (!n_funcs, a, b) in
            TypeHashtbl.add v b res;
            res)
    | None ->
        let h = TypeHashtbl.create 1 in
        n_funcs := !n_funcs + 1;
        let res = `Func (!n_funcs, a, b) in
        TypeHashtbl.add h b res;
        TypeHashtbl.add funcs a h;
        res

let tuple =
  let tuples : t TypeListHashtbl.t = TypeListHashtbl.create 100 in
  let n_tuples = ref 0 in
  fun (ts : t list) ->
    match TypeListHashtbl.find_opt tuples ts with
    | Some i -> i
    | None ->
        n_tuples := !n_tuples + 1;
        let res = `Tuple (!n_tuples, ts) in
        TypeListHashtbl.add tuples ts res;
        res

let count typ =
  (* for debugging *)
  let visit = TypeHashtbl.create 0 in
  let rec count' (typ : t) =
    if TypeHashtbl.mem visit typ then 0
    else (
      TypeHashtbl.add visit typ ();
      match typ with
      | #typevar_t -> 1
      | `Unit | `Int | `Bool -> 1
      | `Tuple (_, ts) -> List.map count' ts |> List.fold_left ( + ) 1
      | `Func (_, a, b) -> 1 + count' a + count' b)
  in
  count' typ

let count_all typ =
  (* for debugging *)
  let sum = TypeHashtbl.create 0 in
  let rec count_all' typ = memo sum count_all'' typ
  and count_all'' typ =
    match typ with
    | #typevar_t -> 1
    | `Unit | `Int | `Bool -> 1
    | `Tuple (_, ts) -> List.map count_all' ts |> List.fold_left ( + ) 1
    | `Func (_, a, b) -> 1 + count_all' a + count_all' b
  in
  count_all' typ

let _ =
  assert (
    count (tuple [ tuple [ tuple [ `Int; `Int ]; `Int ]; tuple [ `Int; `Int ] ])
    = 4);
  assert (
    count_all
      (tuple [ tuple [ tuple [ `Int; `Int ]; `Int ]; tuple [ `Int; `Int ] ])
    = 9)

let rec mapsto return_typ (arg_typ : t list) =
  match arg_typ with
  | [] -> raise (Invalid_argument "[]")
  | [ typ ] -> func (typ, return_typ)
  | a :: tail -> func (a, mapsto return_typ tail)

let () =
  assert (
    [ `Int; `Int; `Int; `Int ] |> mapsto `Bool
    = func (`Int, func (`Int, func (`Int, func (`Int, `Bool)))))

let new_typevar : unit -> typevar_t =
  let id = ref 0 in
  fun () ->
    let res = `TypeVar !id in
    id := !id + 1;
    res

let string_of_typevar (`TypeVar i) = "'" ^ string_of_int i

let () =
  if Options.compress_type then ()
  else
    let assert_equal a b = assert (a = string_of b) in
    let tv i = `TypeVar i in
    `Unit |> assert_equal "unit";
    `Int |> assert_equal "int";
    `Bool |> assert_equal "bool";
    tv 1 |> assert_equal "'1";
    tv 42 |> assert_equal "'42";
    [ `Int; `Int ] |> mapsto `Int |> assert_equal "int -> int -> int";
    (* typical binary operator for integers *)
    [ `Int ]
    |> mapsto ([ `Int ] |> mapsto `Int)
    |> assert_equal "int -> int -> int";
    (* typical binary operator for integers *)
    [ `Int; `Bool ] |> mapsto `Int |> assert_equal "int -> bool -> int";
    [ tv 1; tv 1 ] |> mapsto `Bool |> assert_equal "'1 -> '1 -> bool";
    (* equality *)
    [ tv 1 ] |> mapsto (tv 1) |> assert_equal "'1 -> '1";

    (* id x *)
    let f_t = [ tv 1; tv 2 ] |> mapsto (tv 3) in
    [ f_t; tv 2; tv 1 ]
    |> mapsto (tv 3)
    |> assert_equal "('1 -> '2 -> '3) -> '2 -> '1 -> '3"

(* flip f x y = f y x *)

let occurs_in typ (i : typevar_t) =
  match typ with
  | #typevar_t as j -> i = j
  | `Func _ -> TypeVarSet.mem i (fv typ)
  | `Tuple _ -> TypeVarSet.mem i (fv typ)
  (* | `DFunc (_, _) -> TypeVarSet.mem i (fv typ) *)
  | `Int | `Bool | `Unit -> false

let () =
  let tv i = `TypeVar i in
  let a, b, c = (tv 1, tv 2, tv 3) in
  let test_fv typ ans =
    let res = fv typ in
    List.map tv ans |> TypeVarSet.of_list |> TypeVarSet.equal res
  in
  assert (test_fv `Int []);
  assert (test_fv `Bool []);
  assert (test_fv `Unit []);
  for i = 1 to 100 do
    assert (test_fv (tv i) [ i ])
  done;
  for i = 1 to 10 do
    for j = 1 to 10 do
      assert (test_fv (func (tv i, tv j)) [ i; j ])
    done
  done;
  assert (test_fv (func (`Int, a)) [ 1 ]);
  assert (test_fv (func (`Int, func (`Bool, a))) [ 1 ]);
  assert (
    test_fv
      (func (`Int, func (`Bool, func (a, func (`Int, func (func (c, b), b))))))
      [ 1; 2; 3 ])
