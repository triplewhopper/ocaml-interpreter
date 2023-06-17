type pattern =
  | PInt of int
  | PBool of bool
  | PVar of string
  | PCon of string * pattern list
  (* | PTuple of pattern list
  | PNil
  | PCons of pattern * pattern *)

let ( >>= ) = Result.bind

let check_linearity p =
  let table = ref [] in
  let rec check_linearity' p =
    match p with
    | PInt _ | PBool _ -> Ok ()
    | PVar x ->
        if List.mem x !table then Error x
        else (
          table := x :: !table;
          Ok ())
    | PCon (_, ps) ->
        List.fold_left
          (fun acc p -> acc >>= fun () -> check_linearity' p)
          (Ok ()) ps
    (* | PTuple ps ->
        List.fold_left
          (fun acc p -> acc >>= fun () -> check_linearity' p)
          (Ok ()) ps
    | PCons (p1, p2) -> check_linearity' p1 >>= fun () -> check_linearity' p2 *)
  in
  check_linearity' p

let string_of_pattern p =
  let rec s' = function
    | PInt i -> string_of_int i
    | PBool b -> string_of_bool b
    | PVar x -> x
    | PCon (con, []) -> con
    | PCon (con, ps) -> con ^ "(" ^ String.concat ", " (List.map s' ps) ^ ")"
    (* | PNil -> "[]"
    | PCons (p1, p2) -> s' p1 ^ "::" ^ s' p2 *)
  in
  s' p
