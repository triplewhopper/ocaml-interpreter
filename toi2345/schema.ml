module TypeVarSet = Type.TypeVarSet

type schema = { polys : TypeVarSet.t; fv : TypeVarSet.t; body : Type.t }

let schema polys body =
  { polys; fv = TypeVarSet.diff (Type.fv body) polys; body }

let from_monomorphic_typevar x =
  {
    polys = TypeVarSet.empty;
    fv = TypeVarSet.singleton x;
    body = (x :> Type.t);
  }

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
        (xs :> Type.t list)
        |> List.map Type.string_of |> String.concat " " |> Printf.sprintf "%s. "
      in
      let s_polys =
        if TypeVarSet.is_empty polys then ""
        else string_of_list (TypeVarSet.elements polys)
      in
      Printf.sprintf "%s%s" s_polys (Type.string_of body)

let string_of_senv (env : SchemaEnv.t) =
  Printf.sprintf "(fv:[%s]) {%s}"
    ((env.fv |> Type.TypeVarSet.elements :> Type.t list)
    |> List.map Type.string_of |> String.concat ", ")
    (List.map
       (fun (k, v) -> Printf.sprintf "\"%s\": %s" k (string_of_schema v))
       env.env
    |> String.concat "; ")
