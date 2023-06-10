### toi

1.$
\sigma_1=
\left[
    \alpha \coloneqq \text{Int}, 
    \beta \coloneqq \text{Int} \rightarrow \text{Int} 
\right]
$
2. 単一化子が存在しない
3. $\sigma_3=\left[\alpha \coloneqq \text{Int}, \beta \coloneqq \text{Int}\right]$
4. $\sigma_4=\left[\alpha_1 \coloneqq \beta_1 \rightarrow \beta_2, \alpha_2 \coloneqq \beta_1 \rightarrow \beta_2, \alpha_3 \coloneqq \beta_1 \rightarrow \beta_2\right]$
5. 
$$\begin{aligned}
&\text{unify}\left(
    \left\{
        \alpha\rightarrow\alpha = \beta\rightarrow\gamma,
        \gamma = \text{Int} \rightarrow \beta
    \right\}\right) \\ 
=\ &\text{unify}\left(\left\{
    \alpha = \beta, 
    \alpha = \gamma, 
    \gamma = \text{Int} \rightarrow \beta
\right\}\right) \\
=\ &\text{unify}\left(\left[\alpha \coloneqq \beta \right]\left\{ 
    \alpha = \gamma, 
    \gamma = \text{Int} \rightarrow \beta
\right\}\right) \circ \left[\alpha \coloneqq \beta \right] \\
=\ &\text{unify}\left(\left\{ 
    \beta = \gamma, 
    \gamma = \text{Int} \rightarrow \beta          
\right\}\right) \circ \left[\alpha \coloneqq \beta \right] \\
=\ &\left(\text{unify}\left(\left[\beta \coloneqq \gamma\right]\left\{
    \gamma = \text{Int} \rightarrow \beta          
\right\}\right)\circ \left[\beta \coloneqq \gamma\right]\right) \circ \left[\alpha \coloneqq \beta \right] \\
=\ &\left(\text{unify}\left(\left\{
    \gamma = \text{Int} \rightarrow \gamma        
\right\}\right)\circ \left[\beta \coloneqq \gamma\right]\right) \circ \left[\alpha \coloneqq \beta \right]
\end{aligned}
$$

$\gamma$が$\text{Int}\rightarrow\gamma$に出現するので単一化子は存在しない。

### toi2

まずは`type.ml`で
```ocaml
type typevar_t = [ `TypeVar of int ]

type t = (* Type.t *)
  [ `Int
  | `Bool
  | `Unit
  | `Func of t * t
  | `TypeVar of int]
```
と型`Type.t`と型変数`Type.typevar_t`を定義する.
それに加えて、型変数の集合を
```ocaml
module TypeVarSet = Set.Make (struct
  type t = typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)
```
と定義する。

型推論のアルゴリズムの実装は主に`infer.ml`にある.
```ocaml
module Substitutes = Map.Make (struct
  type t = Type.typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)
```
により、型代入の型を`Type.t Substitutes.t`と定義できる.

型代入$\sigma$と型$t$を受け取り，$\sigma(t)$を返す関数`apply_subst`を以下のように定義する.
```ocaml
let apply_subst (substs : Type.t Substitutes.t) typ =
  let fv = Type.fv typ in
  let intersection =
    if Type.TypeVarSet.cardinal fv < Substitutes.cardinal substs then
      Type.TypeVarSet.fold
        (fun x acc ->
          match Substitutes.find_opt x substs with
          | None -> acc
          | Some v -> Substitutes.add x v acc)
        fv Substitutes.empty
    else Substitutes.filter (fun k _ -> Type.TypeVarSet.mem k fv) substs
  in
  Substitutes.fold (fun alpha t typ -> Type.subst typ alpha t) intersection typ

```
流れは概ね
1. $t$に自由に出現する型変数の集合$FV(t)$を求める.
$FV(t)$は以下のように再帰的に定義される.
$$
\begin{aligned}
FV(\alpha) &= \left\{\alpha\right\}\\
FV(a\rightarrow b) &= FV(a) \cup FV(b) \\
FV(\text{Int})&=\emptyset \\
FV(\text{Bool})&=\emptyset \\
FV(\text{Unit})&=\emptyset
\end{aligned}
$$
実装上は`(Type.t, TypeVarSet.t) Hashtbl.t`を使ってmemoizationを行った.

2. $\sigma=\left[\alpha_i\coloneqq t_i\right]_{i=1}^n$として$FV(t) \cap \left\{\alpha_i \right\}_{i=1}^n$を求める.
3. 2で求めた共通部分は型代入にとって必要最小限の型変数の集合で、その集合の要素ごとに対して`Type.subst`関数を呼び出して`t`
```ocaml
let subst typ (alpha : typevar_t) y =
  (* substitute typevar x in typ with type y *)
  let rec subst' typ (alpha : typevar_t) y =
    match typ with
    | #typevar_t as beta -> if beta = alpha then y else typ
    | `Func (a, b) ->
        if TypeVarSet.mem alpha (fv typ) then
          func (subst' a alpha y, subst' b alpha y)
        else typ
    | `Int | `Bool | `Unit -> typ
  in
  (match y with
  | #typevar_t -> assert true
  | _ -> assert (not (alpha |> occurs_in y)));
  if alpha |> occurs_in typ then subst' typ alpha y else typ

```