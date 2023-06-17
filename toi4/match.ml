open Pattern
(* open Value *)

(* let ( let* ) = Option.bind *)

exception MatchFailed

(* let find_match p v : (string * value) list option =
  let rec find_match' p v bindings : (string * value) list option =

    match (p, v) with
    | PInt i, VInt j -> if i = j then Some bindings else None
    | PBool true, VBool true -> Some bindings
    | PBool false, VBool false -> Some bindings
    | PVar x, _ -> Some ((x, v) :: bindings)
    | PCon ("tuple", ps), VTuple vs ->
        if List.length ps <> List.length vs then None
        else
          List.fold_left2
            (fun acc p v ->
              let* acc = acc in
              find_match' p v acc)
            (Some bindings) ps vs
    | PCon ("[]", []), VList [] -> Some bindings
    | PCon ("[]", _), VList _ -> None
    | PCon ("::", [ p1; p2 ]), VList (v1 :: v2) ->
        let* env1 = find_match' p1 v1 bindings in
        find_match' p2 (VList v2) env1
    | PCon ("::", _), VList [] -> None
    | PCon (con, args), _ ->
        Printf.sprintf "find_match': unknown constructor %s (arity=%d)" con
          (List.length args)
        |> failwith
    | _ -> None
  in 

  let* bindings = find_match' p v [] in
  (* Printf.printf "bindings: {%s}\n" (String.concat "; " (List.map (fun (x, v) -> Printf.sprintf "%s: %s" x (string_of_value v)) bindings)); *)
  Some (List.rev bindings) *)

let rec get_names p =
  match p with
  | PInt _ -> []
  | PBool _ -> []
  | PVar x -> [ x ]
  | PCon (_, args) -> List.concat_map get_names args
(* 
let () =
  assert (find_match (PInt 1) (VInt 1) = Some []);
  assert (find_match (PInt 1) (VInt 2) = None);
  assert (find_match (PBool true) (VBool true) = Some []);
  assert (find_match (PBool true) (VBool false) = None);
  assert (find_match (PVar "x") (VInt 1) = Some [ ("x", VInt 1) ]);
  assert (find_match (PVar "x") (VBool true) = Some [ ("x", VBool true) ]);
  assert (
    find_match (PVar "x") (VTuple [ VInt 1; VBool true ])
    = Some [ ("x", VTuple [ VInt 1; VBool true ]) ]);
  assert (
    find_match
      (PCon ("tuple", [ PVar "x"; PVar "y" ]))
      (VTuple [ VInt 1; VBool true ])
    = Some [ ("x", VInt 1); ("y", VBool true) ]) *)
