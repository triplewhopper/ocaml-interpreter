type 'a t = (string * 'a) list

let empty : 'a t = []
let extend x v (env : 'a t) = (x, v) :: env


let extends xs vs (env : 'a t) =
  List.fold_left2 (fun acc x v -> acc |> extend x v) env xs vs

let lookup x (env : 'a t) = List.assoc x env
let lookup_opt x (env : 'a t) = List.assoc_opt x env

let mem x (env: 'a t) = List.mem_assoc x env
let map f (env: 'a t) = List.map f env