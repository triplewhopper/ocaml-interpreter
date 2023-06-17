type typevar_t = [ `TypeVar of int ]

module TypeVarSet = Set.Make (struct
  type t = typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)

type t_ = t
and t = [ `TyCon of string * int * t list | typevar_t ]
(* [ ty_int
   | ty_bool
   | ty_unit
   | `Func of int * t * t
   | `Tuple of int * t list
   | `TypeVar of int ] *)

let tycon_func = "->"
let tycon_tuple = "tuple"
let tycon_int = "int"
let tycon_bool = "bool"
let tycon_unit = "unit"
let tycon_list = "list"
let is_typevar = function `TypeVar _ -> true | _ -> false

let is_func = function
  | `TyCon (con, _, _) when con = tycon_func -> true
  | _ -> false

let is_tuple = function
  | `TyCon (con, _, _) when con = tycon_tuple -> true
  | _ -> false

let is_func_or_tuple = function
  | `TyCon (con, _, _) when con = tycon_func || con = tycon_tuple -> true
  | _ -> false

let equal a b =
  match (a, b) with
  | `TyCon (_, i, _), `TyCon (_, j, _) -> i = j
  (* | ty_int, ty_int -> true
     | ty_bool, ty_bool -> true
     | ty_unit, ty_unit -> true *)
  | `TypeVar i, `TypeVar j -> i = j
  (* | `Tuple (i, _), `Tuple (j, _) -> i = j
     | `Func (i, _, _), `Func (j, _, _) -> i = j *)
  | _ -> false

let hash t =
  match t with
  | `TyCon (_, i, _) -> (2 * i) + 1
  (* | ty_int -> -3
     | ty_bool -> -2
     | ty_unit -> -1 *)
  | `TypeVar i -> 2 * i
(* | `Tuple (i, _) -> (3 * i) + 1
   | `Func (i, _, _) -> (3 * i) + 2 *)

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

let report_unknown_type_constructor con arity =
  Printf.sprintf "unknown type constructor %s (arity = %d)" con arity
  |> failwith

let compressed_string_of typ =
  let table = TypeHashtbl.create 0 in
  let rec s' typ =
    match typ with
    | `TyCon (con, _, []) -> con
    | `TypeVar i -> Printf.sprintf "'%d" i
    | `TyCon (con, id, ts) when con = tycon_tuple ->
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
    | `TyCon (con, id, [ a; b ]) when con = tycon_func ->
        if TypeHashtbl.mem table typ then Printf.sprintf "<%d>" id
        else (
          TypeHashtbl.add table typ ();
          if (not (TypeHashtbl.mem table a)) && is_func a then
            Printf.sprintf "(%s) -> %s as %d" (s' a) (s' b) id
          else Printf.sprintf "%s -> %s as %d" (s' a) (s' b) id)
    | `TyCon (con, _, args) ->
        report_unknown_type_constructor con (List.length args)
  in
  s' typ

let rec string_of typ : string =
  if Options.compress_type then compressed_string_of typ
  else
    match typ with
    | `TyCon (con, _, []) -> con
    | `TypeVar i -> Printf.sprintf "'%d" i
    | `TyCon (con, _, ts) when con = tycon_tuple ->
        List.map
          (fun t ->
            let s = string_of t in
            if is_func_or_tuple t then "(" ^ s ^ ")" else s)
          ts
        |> String.concat " * "
    | `TyCon (con, _, [ (`TyCon (con_a, _, _) as a); b ])
      when con = tycon_func && con_a = tycon_func ->
        Printf.sprintf "(%s) -> %s" (string_of a) (string_of b)
    | `TyCon (con, _, [ a; b ]) when con = tycon_func ->
        Printf.sprintf "%s -> %s" (string_of a) (string_of b)
    | `TyCon (con, _, [ (`TyCon (con', _, _) as a) ])
      when con = tycon_list && (con' = tycon_func || con' = tycon_tuple) ->
        Printf.sprintf "(%s) list" (string_of a)
    | `TyCon (con, _, [ a ]) when con = tycon_list ->
        Printf.sprintf "%s list" (string_of a)
    | `TyCon (con, _, args) ->
        report_unknown_type_constructor con (List.length args)

let fv =
  let table = TypeHashtbl.create 0 in
  let rec fv' typ = memo table fv'' typ
  and fv'' typ =
    match typ with
    | #typevar_t as a -> TypeVarSet.singleton a
    | `TyCon (_, _, []) -> TypeVarSet.empty
    | `TyCon (_, _, [ a ]) -> fv' a
    | `TyCon (_, _, [ a; b ]) -> TypeVarSet.union (fv' a) (fv' b)
    | `TyCon (_, _, ts) ->
        List.rev_map fv' ts |> List.fold_left TypeVarSet.union TypeVarSet.empty
  in
  fv'

let constr =
  let constrs = Hashtbl.create 100 in
  let n_types = ref 0 in
  fun (con : string) (ts : t list) ->
    match Hashtbl.find_opt constrs con with
    | Some v -> (
        match TypeListHashtbl.find_opt v ts with
        | Some v -> v
        | None ->
            n_types := !n_types + 1;
            let res = `TyCon (con, !n_types, ts) in
            TypeListHashtbl.add v ts res;
            res)
    | None ->
        let h = TypeListHashtbl.create 1 in
        n_types := !n_types + 1;
        let res = `TyCon (con, !n_types, ts) in
        TypeListHashtbl.add h ts res;
        Hashtbl.add constrs con h;
        res

let ty_int = constr tycon_int []
let ty_bool = constr tycon_bool []
let ty_unit = constr tycon_unit []
let ty_list t = constr tycon_list [ t ]
let func (a, b) = constr tycon_func [ a; b ]
(* let funcs : t TypeHashtbl.t TypeHashtbl.t = TypeHashtbl.create 100 in
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
         res *)

let tuple ts = constr tycon_tuple ts
(* let tuples : t TypeListHashtbl.t = TypeListHashtbl.create 100 in
   let n_tuples = ref 0 in
   fun (ts : t list) ->
     match TypeListHashtbl.find_opt tuples ts with
     | Some i -> i
     | None ->
         n_tuples := !n_tuples + 1;
         let res = `Tuple (!n_tuples, ts) in
         TypeListHashtbl.add tuples ts res;
         res *)

let count typ =
  (* for debugging *)
  let visit = TypeHashtbl.create 0 in
  let rec count' (typ : t) =
    if TypeHashtbl.mem visit typ then 0
    else (
      TypeHashtbl.add visit typ ();
      match typ with
      | #typevar_t -> 1
      | `TyCon (_, _, ts) -> List.map count' ts |> List.fold_left ( + ) 1)
  in
  count' typ

let count_all typ =
  (* for debugging *)
  let sum = TypeHashtbl.create 0 in
  let rec count_all' typ = memo sum count_all'' typ
  and count_all'' typ =
    match typ with
    | #typevar_t -> 1
    | `TyCon (_, _, ts) -> List.map count_all' ts |> List.fold_left ( + ) 1
  in
  count_all' typ

let _ =
  assert (
    count
      (tuple
         [
           tuple [ tuple [ ty_int; ty_int ]; ty_int ]; tuple [ ty_int; ty_int ];
         ])
    = 4);
  assert (
    count_all
      (tuple
         [
           tuple [ tuple [ ty_int; ty_int ]; ty_int ]; tuple [ ty_int; ty_int ];
         ])
    = 9)

let rec mapsto return_typ (arg_typ : t list) =
  match arg_typ with
  | [] -> raise (Invalid_argument "[]")
  | [ typ ] -> func (typ, return_typ)
  | a :: tail -> func (a, mapsto return_typ tail)

let () =
  assert (
    [ ty_int; ty_int; ty_int; ty_int ]
    |> mapsto ty_bool
    = func (ty_int, func (ty_int, func (ty_int, func (ty_int, ty_bool)))))

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
    ty_unit |> assert_equal "unit";
    ty_int |> assert_equal "int";
    ty_bool |> assert_equal "bool";
    tv 1 |> assert_equal "'1";
    tv 42 |> assert_equal "'42";
    [ ty_int; ty_int ] |> mapsto ty_int |> assert_equal "int -> int -> int";
    (* typical binary operator for integers *)
    [ ty_int ]
    |> mapsto ([ ty_int ] |> mapsto ty_int)
    |> assert_equal "int -> int -> int";
    (* typical binary operator for integers *)
    [ ty_int; ty_bool ] |> mapsto ty_int |> assert_equal "int -> bool -> int";
    [ tv 1; tv 1 ] |> mapsto ty_bool |> assert_equal "'1 -> '1 -> bool";
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
  | `TyCon _ -> TypeVarSet.mem i (fv typ)

let () =
  let tv i = `TypeVar i in
  let a, b, c = (tv 1, tv 2, tv 3) in
  let test_fv typ ans =
    let res = fv typ in
    List.map tv ans |> TypeVarSet.of_list |> TypeVarSet.equal res
  in
  assert (test_fv ty_int []);
  assert (test_fv ty_bool []);
  assert (test_fv ty_unit []);
  for i = 1 to 100 do
    assert (test_fv (tv i) [ i ])
  done;
  for i = 1 to 10 do
    for j = 1 to 10 do
      assert (test_fv (func (tv i, tv j)) [ i; j ])
    done
  done;
  assert (test_fv (func (ty_int, a)) [ 1 ]);
  assert (test_fv (func (ty_int, func (ty_bool, a))) [ 1 ]);
  assert (
    test_fv
      (func
         (ty_int, func (ty_bool, func (a, func (ty_int, func (func (c, b), b))))))
      [ 1; 2; 3 ])
