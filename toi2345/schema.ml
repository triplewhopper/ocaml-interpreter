module TypeVarSet = Type.TypeVarSet
type schema = { polys : TypeVarSet.t; fv : TypeVarSet.t; body : Type.t }


let schema polys body=
  { polys; fv = TypeVarSet.diff (Type.fv body) polys; body }

module SchemaEnv = struct
  type t = { env : schema Env.t; fv : Type.TypeVarSet.t }
  type elt = schema

  let empty : t = { env = Env.empty; fv = Type.TypeVarSet.empty }

  let extend (x : string) (v : elt) (env : t) =
    {
      env = env.env |> Env.extend x v;
      fv = v.fv |> Type.TypeVarSet.union env.fv;
    }

  let extends (x : string list) (v : elt list) (env : t) =
    {
      env = env.env |> Env.extends x v;
      fv =
        v
        |> List.fold_left
             (fun acc (v : elt) -> v.fv |> Type.TypeVarSet.union acc)
             env.fv;
    }

  let map f env : t =
    List.fold_right (fun (k, v) acc -> extend k (f v) acc) env.env empty

  let lookup (x : string) (env : t) = env.env |> Env.lookup x
end

let string_of_schema : schema -> string = function
  | { polys; fv = _; body } ->
      let string_of_list xs =
        (xs :> Type.t list) |> List.map Type.string_of 
        |> String.concat " " |> Printf.sprintf "%s. "
      in
      let s_polys =
        if TypeVarSet.is_empty polys then ""
        else string_of_list (TypeVarSet.elements polys)
      in
      Printf.sprintf "%s%s" s_polys (Type.string_of body)

let string_of_schema_debug : schema -> string = function
  | { polys; fv; body } ->
      let string_of_list xs =
        List.map Type.string_of (xs :> Type.t list)
        |> String.concat "; " |> Printf.sprintf "[%s]"
      in
      let s_polys = string_of_list (TypeVarSet.elements polys) in
      Printf.sprintf "{polys=%s; fv=%s; body=%s}" s_polys
        (string_of_list (TypeVarSet.elements fv))
        (Type.string_of body)
