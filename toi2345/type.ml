type typevar_t = [ `TypeVar of int ]

let () = Printexc.record_backtrace true

module TypeVarSet = Set.Make (struct
  type t = typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)

type t =
  [ `Int
  | `Bool
  | `Unit
  | `Func of t * t
  | `TypeVar of int (*| `DFunc of t * t *) ]

module UFSet = struct
  let father, rk = (Hashtbl.create 0, Hashtbl.create 0)

  type elt = typevar_t

  let rank (x : elt) =
    match Hashtbl.find_opt rk x with
    | Some r -> r
    | None ->
        Hashtbl.add rk x 0;
        0

  let rec f x =
    match Hashtbl.find_opt father x with
    | Some x' ->
        if x = x' then x
        else
          let f' = f x' in
          Hashtbl.replace father x f';
          f'
    | None ->
        Hashtbl.add father x x;
        x

  let rec simplify typ =
    match typ with
    | `Int | `Bool | `Unit -> typ
    | `Func (t1, t2) -> `Func (simplify t1, simplify t2)
    | #typevar_t as beta -> (f beta :> t)

  let merge x1 x2 =
    let f1, f2 = (f x1, f x2) in
    assert (f1 <> f2);
    let c = rank f1 - rank f2 in
    if c > 0 then Hashtbl.replace father f2 f1 else Hashtbl.replace father f1 f2;
    if c = 0 then
      let rk_f2 = Hashtbl.find rk f2 in
      Hashtbl.replace rk f2 (rk_f2 + 1)
end

let rec fv =
  let table = Hashtbl.create 100 in
  fun typ ->
    match typ with
    | #typevar_t as a -> TypeVarSet.singleton a
    | `Unit | `Int | `Bool -> TypeVarSet.empty
    | `Func (a, b) -> (
        match Hashtbl.find_opt table typ with
        | Some fv -> fv
        | None ->
            let u = TypeVarSet.union (fv a) (fv b) in
            Hashtbl.add table typ u;
            u)

let func (a, b) = `Func (a, b)
(* let dfunc (a, b) = `DFunc (a, b) *)

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

let rec string_of : t -> string = function
  | `Int -> "int"
  | `Bool -> "bool"
  | `Unit -> "unit"
  | `TypeVar i -> "'" ^ string_of_int i
  | `Func ((`Func _ (*| `DFunc _ *) as a), b) ->
      Printf.sprintf "(%s) -> %s" (string_of a) (string_of b)
  | `Func (a, b) -> Printf.sprintf "%s -> %s" (string_of a) (string_of b)
(* | `DFunc (((`Func _|`DFunc _) as a), b) ->
       Printf.sprintf "(%s) ~> %s" (string_of a) (string_of b)
   | `DFunc (a, b) -> Printf.sprintf "%s ~> %s" (string_of a) (string_of b) *)

let () =
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
  | `Func (_, _) -> TypeVarSet.mem i (fv typ)
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

let subst typ (alpha : typevar_t) y =
  (* substitute typevar x in typ with type y *)
  let rec subst' typ (alpha : typevar_t) y =
    match typ with
    | #typevar_t as beta -> if beta = alpha then y else typ
    | `Func (a, b) ->
        if TypeVarSet.mem alpha (fv typ) then
          func (subst' a alpha y, subst' b alpha y)
        else typ
    (* | `DFunc (a, b) ->
        if TypeVarSet.mem alpha (fv typ) then
          dfunc (subst' a alpha y, subst' b alpha y)
        else typ *)
    | `Int | `Bool | `Unit -> typ
  in
  (match y with
  | #typevar_t -> assert true
  | _ -> assert (not (alpha |> occurs_in y)));
  if alpha |> occurs_in typ then subst' typ alpha y else typ

let () =
  let a, b, c = (`TypeVar 1, `TypeVar 2, `TypeVar 3) in
  let faa, fab, fba, fbb =
    (func (a, a), func (a, b), func (b, a), func (b, b))
  in
  try
    assert (subst `Int a `Int = `Int);
    assert (subst `Bool a `Int = `Bool);
    assert (subst `Bool a `Int = `Bool);
    assert (subst `Bool a `Bool = `Bool);
    assert (subst faa a a = faa);
    assert (subst faa a b = fbb);
    assert (subst faa b a = faa);
    assert (subst faa b b = faa);
    assert (subst fab a a = fab);
    assert (subst fab a b = fbb);
    assert (subst fab b a = faa);
    assert (subst fab b b = fab);
    assert (subst fba a a = fba);
    assert (subst fba a b = fbb);
    assert (subst fba b a = faa);
    assert (subst fba b b = fba);
    assert (subst fbb a a = fbb);
    assert (subst fbb a b = fbb);
    assert (subst fbb b a = faa);
    assert (subst fbb b b = fbb);
    assert (
      subst (func (func (func (b, b), func (b, b)), func (b, b))) b a
      = func (func (func (a, a), func (a, a)), func (a, a)));
    assert (
      subst (func (func (func (b, b), func (`Int, b)), func (b, b))) b a
      = func (func (func (a, a), func (`Int, a)), func (a, a)));
    assert (
      subst (func (func (func (b, c), func (`Int, b)), func (c, b))) b a
      = func (func (func (a, c), func (`Int, a)), func (c, a)))
  with Assert_failure _ as e ->
    Printf.printf "error: %s\n" (Printexc.to_string e);
    Printexc.print_backtrace stdout
