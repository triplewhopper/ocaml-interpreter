update:
- removed support for `dfun`.
- fixed type unsoundness in `let rec` 
  ex.
  - `let rec f x = (f x, f x);;`
   from `'a -> 'b * 'b`
    to `Error: Recursive occurence of ...`
  - `let rec f n x y = if n = 0 then (x, y) else f n y x;;`
    from `'a 'b. int -> 'a -> 'b -> 'a * 'b`
      to `'a. int -> 'a -> 'a -> 'a * 'a`
### ビルド方法
```bash
$ cd 08-231017
$ ls
dune-project report.md    report.pdf   toi2345
$ cd toi2345
$ ls
bindings.ml  dune         eval.ml      infer.ml     lexer.mll    options.ml   schema.ml    type.ml
command.ml   env.ml       expr.ml      input.in     main.ml      parser.mly   transform.ml value.ml
$ dune build
Entering directory '.../08-231017'
File "toi2345/parser.mly", line 20, characters 22-26:
Warning: the token DFUN is unused.
$ ./main.exe
# 1;;
- : int = 1
# 2;;
- : int = 2
# let rec f x  =f x;;
val f: '6 '7. '6 -> '7 = <fun (x)>
# %(press Ctrl+D or Ctrl+C)
$
```

### toi1
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

$\gamma$ が $\text{Int}\rightarrow\gamma$ に出現するので単一化子は存在しない. 

### toi2

#### 背景
まずは`type.ml`で
```ocaml
type typevar_t = [ `TypeVar of int ]

type t = (* Type.t *)
  [ `Int
  | `Bool
  | `Unit
  | `Func of int * t * t 
  | `Tuple of int * t list (* length >=2 *)
  | `TypeVar of int ]
```
と型`Type.t`と型変数`Type.typevar_t`を定義する.
それに加えて, 型変数の集合`TypeVarSet`を
```ocaml
(* type.ml *)
module TypeVarSet = Set.Make (struct
  type t = typevar_t

  let compare (`TypeVar i) (`TypeVar j) = i - j
end)
```
と定義する. 
また, 型をキーとした, 型についてのメモ化を行うためのハッシュテーブル`TypeHashtbl`も定義した. 
`TypeHashtbl`の`equal`と`hash`は簡単で
```ocaml
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
```
つまり, `Tuple`と`Func`を唯一あるIDを付与すれば等しさとハッシュ値は高速に計算できる. そのためにIDを付与するヘルパー関数`func`と`tuple`も定義しなければならない. 

`func`と`tuple`は各自「今まで返した型」を格納するハッシュテーブルとそれを数えるカウンターを維持する. `func a b`や`tuple [t1; t2]`の形で呼び出すとまずハッシュテーブルに問い合わせる. すでにそのかたが存在していればそれを返し, 存在しない場合は新たに作ってハッシュテーブルに登録して返す. 

#### 型代入

型推論のアルゴリズムの実装は主に`infer.ml`にある.
型代入は[Union-Find](https://en.wikipedia.org/wiki/Disjoint-set_data_structure)というデータ構造で表示する.
Union-Findは, 以下の3種類の操作を提供する.
- $\text{union}(C_1, C_2)$
  互いに素である型の集合$C_1$, $C_2$を合併させる
  ここでの集合を同値類と理解しても構わない. 
- $\text{find}(\tau)$
  $\tau$の属する集合の代表元を探す
- $\text{singleton}(\tau)$
  集合$\{\tau\}$をつくる.
Union-Findを実装したモジュール`UnionFind`のシグネチャは以下のようである. 

```ocaml
(* infer.ml *)
module UnionFind: sig
  val find : Type.t -> Type.t 
  val merge : Type.t -> Type.t -> unit (* union *)
  val represent : Type.t -> Type.t
  val apply : Type.t -> Type.t
  val apply_schema : Schema.schema -> Schema.schema
  val string_of_father : unit -> string
end
```
Path compressionとunion by rankという二つの最適化方法を使うと`find`と`merge`は$O(\alpha(n))$の計算量で済ませる. 
ここで$\alpha(n)$は[Ackermann関数の逆関数](https://en.wikipedia.org/wiki/Ackermann_function#Inverse)である. 

型代入$\sigma$と型$t$を受け取り，$\sigma(t)$を返す関数`apply`を以下のように定義する.
`represent`の定義はtoi3を参照してください. 
```ocaml
(* in module UnionFind *)
  let apply t =
    let table = TypeHashtbl.create 0 in
    let rec apply' t = Type.memo table apply'' t
    and apply'' t =
      match t with
      | `Int -> `Int
      | `Bool -> `Bool
      | `Unit -> `Unit
      | `Func (_, t1, t2) -> Type.func (apply' t1, apply' t2)
      | `Tuple (_, ts) -> Type.tuple (List.map apply' ts)
      | `TypeVar _ as beta ->
          let t = represent beta in
          if not (Type.equal beta t) then 
            if beta |> Type.occurs_in t then
              raise (RecursiveOccurenceError (beta, t))
            else apply' t
          else t
    in
    let t' = apply' t in
    assert (Type.equal t' (apply' t));
    t'
```
ここで, $4$行目の`Type.memo`はメモ化においてハッシュテーブルに問い合わせる関数である. 
もし問い合わせに失敗したら, `f`を`t`で呼び出し, 返り値をハッシュテーブルに追加する. 
```ocaml
(* type.ml *)
let memo table f t =
  match TypeHashtbl.find_opt table t with
  | Some v -> v
  | None ->
      let v = f t in
      TypeHashtbl.add table t v;
      v
```

`apply_schema`という型代入を型スキーマに適用するための関数もあるが, それと`apply`の異なる点は, 型スキーマに束縛された変数をそのままにすることだけにある. 
つまり, 
```ocaml
(* infer.ml *)
(* in module UnionFind *)
let apply_schema (s : Schema.schema) =
  ...
    | `TypeVar _ as beta ->
        if Type.TypeVarSet.mem beta s.fv then (* s.fvはsの自由変数の集合 *)
          let t = represent beta in
          if not (Type.equal beta t) then
            if beta |> Type.occurs_in t then
              raise (RecursiveOccurenceError (beta, t))
            else apply' t
          else t
        else beta
  ...
```

### toi3

代入の合成を明示的に行わない. 代入の合成に相当する関数は`UnionFind.merge`と思われる. 
型代入は, あくまで型と型変数の間の同値関係を表すもので, それを実際に行うよりUnionFindで記録する方が効率が良いであろう. 

今までは型の集合の代表元は特に指定していないが, 実は`UnionFind.merge`で各同値類に対して「型変数以外のもの（つまり`Int, Bool, Unit, Func, Tuple`のいずれか, いわゆる型コンストラクタ）が高々一つある」という不変量を維持しなければならない. そのような型がある場合はその型を代表元とし, ない場合は型変数をどれか一つ取り出せば良い. 

例えば, $\{\alpha, \beta, \text{Int}\}$の代表元は$\text{Int}$で, $\{\delta, \gamma\}$の代表元は $\delta$ か $\gamma$ のどちらでも構わない.
同値類を見える化には`UnionFind.string_of_father ()`がある. 

最適化の関係上, `UnionFind.find`は必ずしも望まれる代表元を返すとは限らないので, それとは別に`UnionFind.represent`関数で代表元を取り出す. 
実装上は`representative`というハッシュテーブルで型変数以外の代表元を格納することにした. 
`find`と`merge`それぞれの中で`representative`に対して維持操作が必要になる. 

まずは`merge`関数
```ocaml
(* infer.ml *)
(* in module UnionFind *)
let father : Type.t TypeHashtbl.t = TypeHashtbl.create 0
let rk : int TypeHashtbl.t = TypeHashtbl.create 0
let representative : Type.t TypeHashtbl.t = TypeHashtbl.create 0

let merge x1 x2 =
  let f1, f2 = (find x1, find x2) in
  if not (Type.equal f1 f2) then (
    (*維持操作*)
    if not (Type.is_typevar f1) then TypeHashtbl.replace representative f2 f1;
    if not (Type.is_typevar f2) then TypeHashtbl.replace representative f1 f2;
    (*以上の 2 つの if 文のうち多くとも 1 つが成り立つ*)
    let c = rank f1 - rank f2 in
    (* union by rank *)
    if c > 0 then TypeHashtbl.replace father f2 f1
    else TypeHashtbl.replace father f1 f2;
    if c = 0 then
      let rk_f2 = TypeHashtbl.find rk f2 in
      TypeHashtbl.replace rk f2 (rk_f2 + 1))
```

$\text{singleton}(\tau)$と$\text{find}(\tau)$は, 実装上に`find`に統一された.
```ocaml
(* infer.ml *)
(* in module UnionFind *)
let rec find x =
  match TypeHashtbl.find_opt father x with
  | Some x' ->
      if Type.equal x x' then x
      else
        let f' = find x' in
        (* Path compression *)
        TypeHashtbl.replace father x f';
        f'
  | None ->
      TypeHashtbl.add father x x;
      (*維持操作*)
      if not (Type.is_typevar x) then TypeHashtbl.add representative x x;
      x
```
よって`represent`関数は以下のように実装できる
```ocaml
(* infer.ml *)
(* in module UnionFind *)
let represent x =
  let f = find x in
  match TypeHashtbl.find_opt representative f with Some x' -> x' | None -> f
```
### toi4
Union-Findで単一化アルゴリズムは長さ$n$の型制限リストに対して$O(n\cdot\alpha(n))$の計算量で終わらせる.

その上で単一化アルゴリズムは以下のように実装された. 
```ocaml
(* infer.ml *)
type constraint_t = Type.t * Type.t
...
let rec unify (cs : constraint_t list): unit =
  let rec unify' (tau, nu) =
    let tau = UnionFind.represent (UnionFind.find tau) in
    let nu = UnionFind.represent (UnionFind.find nu) in
    match (tau, nu) with
    | `Int, `Int | `Bool, `Bool | `Unit, `Unit -> ()
    | `Func (_, a, b), `Func (_, a', b') ->
        unify' (a, a');
        unify' (b, b')
    | `Tuple (_, ts), `Tuple (_, ts') ->
        if List.length ts <> List.length ts' then
          raise (BadConstraintError (tau, nu))
        else List.iter2 (fun t t' -> unify' (t, t')) ts ts'
    | c, (`TypeVar _ as alpha) | (`TypeVar _ as alpha), c ->
        UnionFind.merge alpha c
    | _ -> raise (BadConstraintError (tau, nu))
  in
  List.iter unify' cs
```
出現検査も必要のはずであるが, `unify'`のなかで行うと効率が悪いと言われるので
型代入を型に適用する時（`UnionFind.apply t`）に先伸ばされた. 
単一化に成功すれば, `UnionFind.apply t`で`t`の中に出現する型変数をできるだけ具体的な型に置き換えることができる. 

### toi5
型スキーマの定義は`schmea.ml`にあり
```ocaml
(* schema.ml *)
module TypeVarSet = Type.TypeVarSet
type schema = { polys : TypeVarSet.t; fv : TypeVarSet.t; body : Type.t }
```
束縛変数の集合は`polys`で, 自由変数の集合は`fv`である. 
型スキーマを作るためのヘルパー関数`Schema.schema`も定義した. 
`Type.fv`は型の中の型変数集合を求める関数である. （メモ化あり）
```ocaml
(* schema.ml *)
let schema polys body =
  { polys; fv = TypeVarSet.diff (Type.fv body) polys; body }
```
また, 型スキームの環境として`schema Env.t`を本来使うべきだったが, 自由変数の集合の問い合わせに対応するために, 自由変数の集合を同時に維持した`SchemaEnv`モジュールを定義した. 

Let多相に対応させるためには（インタプリタの環境中の）変数（`EVar x`）が引用されるときに都度`instantiate`し, let式で式を変数名に束縛するとき`generalize`を行わなければならない. 
具体的に言えば, `infer_expr`で`EVar x`に対して`instantiate`を呼び出して, xの型にある束縛変数をすべて新たな型変数で置き換える. 

```ocaml
(* infer.ml *)
let infer_expr (schema_env : SchemaEnv.t) e : Type.t * constraint_t list =
  match e with
  ...
  | `EVar x -> (
      try
        let s = schema_env |> SchemaEnv.lookup x in
        let typ = s |> instantiate in
        (typ, [])
      with Not_found -> raise (Transform.UnboundVariable x)) 
      (* ここの try with は前回課題のdfunに対応すためのlegacy codeで無視していい *)
  ...
```
`EFun (_, var, body)`に対して, `var`の型を「束縛変数のない型スキーマ」（つまり単相的）にして型スキーマ環境に入れて型制限リストを生成する. 
なお, `EFun(_, var, body)`の一番目の`_`は構文解析の時に付与されるIDで今まで役に立ったことはない. 
```ocaml
  | `EFun (_, var, body) ->
      let alpha = Type.new_typevar () in
      let s_alpha = Schema.schema Type.TypeVarSet.empty (alpha :> Type.t) in
      let env' = schema_env |> SchemaEnv.extend var s_alpha in
      let t, c = infer_expr env' body in
      (Type.func ((alpha :> Type.t), t), c)
  ...
```
`ELet((names, e1s), e2)`は, `e1s`リストを走査してそれぞれの型と型制限を求めて`generalize`を呼び出す. 
得られた型スキーマを環境に入れる. 
```ocaml
  | `ELet ((names, e1s), e2) ->
      let ss =
        List.map
          (fun e ->
            let t, c = infer_expr schema_env e in
            let s = generalize c schema_env t in
            s)
          e1s
      in
      let schema_env' = schema_env |> SchemaEnv.extends names ss in
      let t, c = infer_expr schema_env' e2 in
      (t, c)
```
`ELetRec((names, funcs), e2)`はいくつか注意点がある. 
まずは`names`$=[name_1; name_2; \cdots; name_n]$の要素それぞれに対して単相的な型スキーマ$\forall \emptyset.\alpha_i$を生成する. 
つまりPolymorphic recursionをサポートしていない.
これで型スキーマのリスト`schemas`を得る. 
これらの型スキーマを入れた環境`schema_env'`で`funcs`の要素それぞれに対して型推論を行なって, 型のリストと型制限のリストのペア$(t, cs)$のリスト$[(t_1, cs_1); (t_2, cs_2);\cdots;(t_n, cs_n)]$を得る. 

$cs_i$の先頭に
`instantiate (SchemaEnv.lookup schema_env)`$=t_i$ 
という制限を追加して$cs_i'$を得る。
型の順序は逆になっているので`List.rev`する. 
> 例えば, `let rec n1 = f1 and n2 = f2 and n3 = f3 in e`の場合, 
> `names=[n1;n2;n3], funcs=[f1;f2;f3]`として, `List.map infer_expr`で得られたのは`[(t_1, cs_1); (t_2, cs_2); (t_3, cs_3)]`. 
> `infer_expr`の出力する型制限のリストは, 一番最初に生成された制限がリストの最後に, 一番新しい制限がリストの先頭にくるという性質を保たせたいが, 下記のコード$13$行目の`List.fold_left2`の後に$[cs_1; cs_2;\cdots;cs_n]$は$[cs_n'; cs_{n-1}';\cdots;cs_1']$ と逆になっているが, $t_i$の順序**も逆になる**ため一度`List.rev`で呼び出す必要がある.

`g`は`generalize`の部分適用で得られた関数で, 同じ型制限リストと型スキーム環境の下で何度も`generalize`するのを高速化するためのものである. 
`t1s`の要素ごとに対して`g`を呼び出して得た型スキームを環境に入れたら, `e2`の型推論に進む. 
`s2`は`Type.t`であり`Schema.schema`でないので要注意. 

```ocaml
  | `ELetRec ((names, funcs), e2) ->
      let typevars =
        List.init (List.length names) (fun _ ->
            let alpha = Type.new_typevar () in
            alpha)
      in
      let schemas : Schema.schema list =
        List.map (Schema.schema Type.TypeVarSet.empty) (typevars :> Type.t list)
      in
      let schema_env' = schema_env |> SchemaEnv.extends names schemas in
      let t1s, c1s =
        List.map (infer_expr schema_env') funcs
        |> List.fold_left2
             (fun (t1s, c1s) name (t, cs) ->
               let cs' = 
                 let t' = schema_env' |> SchemaEnv.lookup name |> instantiate in
                 (t', t) :: cs 
               in
               (t :: t1s, cs' :: c1s))
             ([], []) names
      in
      let t1s = t1s |> List.rev in
      let c1s' = c1s |> List.concat in
      let g = generalize c1s' schema_env in
      let s1s = t1s |> List.map (fun t -> g t) in
      let s2, c2 = infer_expr (schema_env |> SchemaEnv.extends names s1s) e2 in
      (s2, c2 @ c1s')

```
#### `instantiate`
次は`instantiate`の実装について説明する. 
```ocaml
(* infer.ml *)
let instantiate (s : Schema.schema) : Type.t =
  let table = Hashtbl.create (Type.TypeVarSet.cardinal s.polys) in
  (* table は, 各束縛変数をキーとしてその置き換え先である自由な型変数を値とするハッシュテーブル *)
  Type.TypeVarSet.iter
    (fun alpha -> Hashtbl.add table alpha (Type.new_typevar () :> Type.t))
    s.polys;(* table を 充填する *)
  
  let memory = TypeHashtbl.create 0 in (* メモ化 *)
  let rec instantiate' (t : Type.t) : Type.t = Type.memo memory instantiate'' t
  and instantiate'' = function
    | `Int -> `Int
    | `Bool -> `Bool
    | `Unit -> `Unit
    | `Func (_, t1, t2) as f ->
        (* f の自由変数の集合と s の束縛変数の集合が互いに素ならばさらに再帰する必要がない*)
        if Type.TypeVarSet.disjoint (Type.fv f) s.polys then f
        else Type.func (instantiate' t1, instantiate' t2)
    | `Tuple (_, ts) as tuple ->
        assert (List.length ts = 2);
        (* 上と同様に *)
        if Type.TypeVarSet.disjoint (Type.fv tuple) s.polys then tuple
        else Type.tuple (List.map instantiate' ts)
    | `TypeVar _ as alpha ->
        (* alpha が s.polysに出現する時のみ置き換えを行う *)
        if Type.TypeVarSet.mem alpha s.polys then Hashtbl.find table alpha
        else alpha
  in
  instantiate' s.body
```

#### `generalize`
```ocaml
(* infer.ml *)
let generalize (c : constraint_t list) =
  unify c; 
  fun (env : SchemaEnv.t) ->
    let env' = SchemaEnv.map UnionFind.apply_schema env in
    (*　型スキーム環境の中の型スキーム全体に対して型代入を行う. 
       実は必要なのはenv'への型代入後の自由変数の集合だけであるが, 
       ここが性能のボトルネックになることはまだないので
       そういう素朴な方法のままにした *)
    fun (t : Type.t) ->
      let typ = UnionFind.apply t in
      assert (Type.equal typ (UnionFind.apply typ));
      (* unifyを行った後は冪等な再汎単一化子が得られることを assert で確認する
         c.f. idempotent most general unifier 
         c.f. Lemma 3 in references [1] *)
      let polys = Type.TypeVarSet.diff (Type.fv typ) env'.fv in
      let s = Schema.schema polys typ in
      s
      (*束縛変数の集合＝型typの自由変数から環境の中の自由変数を除いた型変数の集合＝を取り出す *)

```
#### `Type.fv`
自由変数を取り出す`Type.fv`関数は
```ocaml
(* type.ml *)
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

```
`CDecls`と`CRecDecls`の処理はそれぞれ`ELet`と`ELetRec`とほぼ一致していて、ただし`let [rec] ... in e`の`e`についての型推論をしない点を除く.

実行例
```ocaml
# let id x = x and square x = x * x in (id square) (id 42);;
- : int = 1764

# let id x = x;;
val id: '14. '14 -> '14 = <fun (x)>

# let id x = x in (id 1, id true);;
- : int * bool = (1, true)

# (fun x -> (x 1, x true)) id;;
Error: Cannot unify int and bool

# let id x y = y;;
val id: '25 '26. '25 -> '26 -> '26 = <fun (x)>

# let k = id 1;;
val k: '28. '28 -> '28 = <fun (y)>
# (k 1, k true);; 
- : int * bool = (1, true)
(* _weak は実装していない *)

# let rec f x = (f x, f x);;
Error: Recursive occurence of '36 in '36 * '37

# let rec f x = f x;;
val f: '39 '40. '39 -> '40 = <fun (x)>

# let rec even n = if n < 2 then n = 0 else odd (n-1)     
      and  odd n = if n < 2 then n = 1 else even (n-1);;
val even: int -> bool = <fun (n)>
val odd: int -> bool = <fun (n)>

# even 101;;
- : bool = false
# odd 101;;
- : bool = true

# let rec fact x =
    if x <= 1 then 1 else x * fact (x - 1);;
val fact: int -> int = <fun (x)>

# fact 10;;
- : int = 3628800

# let compose f g x = f (g x);;
val compose: '75 '76 '77. ('76 -> '77) -> ('75 -> '76) -> '75 -> '77 = <fun (f)>

# let rec power f n = 
    if n = 0 then fun x -> x 
    else compose f (power f (n - 1));;
val power: '84. ('84 -> '84) -> int -> '84 -> '84 = <fun (f)>

# let zero s z = z;;
val zero: '94 '95. '94 -> '95 -> '95 = <fun (s)>

# let succ n f x = f (n f x);;
val succ: '98 '100 '101. (('100 -> '101) -> '98 -> '100) -> ('100 -> '101) -> '98 -> '101 = <fun (n)>

# let mult m n f x = m (n f) x;; 
val mult: '104 '105 '106 '108. ('106 -> '105 -> '108) -> ('104 -> '106) -> '104 -> '105 -> '108 = <fun (m)>

# let rec make n = if n=0 then zero else succ (make (n-1));;
val make: '115. int -> ('115 -> '115) -> '115 -> '115 = <fun (n)>

# make 10 (fun x -> x + 1) 0;;
- : int = 10

# mult (make 6) (make 15) (fun x -> x+1) 0;;
- : int = 90
```
### hatten1
型代入の適用が必ず止まることを保証するためである. 
(UnionFindを使った単一化は出現検査をしないので単一化は必ず停止する)
例えば
```ocaml
# let f x = x x in f f;;
Error: Recursive occurence of '5 in '5 -> '6
```
の場合, `x`の型は`'5`を`'5 -> '6`, さらに`('5 -> 6) -> '6`, `(('5 -> '6) -> '6) -> '6`と無限にループに落ちい、型代入の適用が停止しない.
出現検査をしないで単一化することはrecursive typesを考えていることに相当する.
例えば上記の型は`(? -> '6) as ?`というような型に相当する.

### hatten2
前述の型推論に対するメモ化を行うことで
`INFER_ONLY=true`という環境変数を追加すると型推論だけが行われる. 
`stderr`に`inference only mode`が出力される. 
型推論が終われば`stderr`に`type inference done.`が出力される. 
`COMPRESS_TYPE=true`という環境変数を追加すると型は圧縮して表示される. 
つまり, 型に唯一の番号を付与して（`xxx as id`という形）, その型が再び出現すれば`<id>`と表す. 
```ocaml
$ rm output.out
$ wc output.out                                      
wc: output.out: open: No such file or directory
$ cat input.in                                       
let x0 x = (x, x) in
  let x1 y = x0 (x0 y) in
  let x2 y = x1 (x1 y) in
  let x3 y = x2 (x2 y) in
  let x4 y = x3 (x3 y) in
  let x5 y = x4 (x4 y) in
  x5 (fun x -> x);;
$ COMPRESS_TYPE=true INFER_ONLY=true ./main.exe < input.in > output.out
Inference only mode
type inference done.
$ cat output.out 
# - : (((((((((((((((((((((((((((((((('32 -> '32 as 153) * <153> as 132) * <132> as 133) 
* <133> as 134) * <134> as 135) * <135> as 136) * <136> as 137) * <137> as 138) * <138> as 
139) * <139> as 140) * <140> as 141) * <141> as 142) * <142> as 143) * <143> as 144) * <144> 
as 145) * <145> as 146) * <146> as 147) * <147> as 148) * <148> as 149) * <149> as 150) * 
<150> as 151) * <151> as 152) * <152> as 153) * <153> as 154) * <154> as 155) * <155> as 156) 
* <156> as 157) * <157> as 158) * <158> as 159) * <159> as 160) * <160> as 161) * <161> as 
162) * <162> as 163
# %                                       
```
上式に現れた型の番号は$153, 132, 133, 134, \cdots, 163$と$33$個ある. $132, \cdots, 163$という$32$個の型は$153$（つまり`'32->'32`, `fun x->x`の型)の出現回数を順次$2$倍にして, 結局153の出現回数は$2^{32}$に上る. 

この式の特徴は, 型を木とすれば重複する部分木がたくさんあるということである. 本質的に違う部分木は32個しかないのに最終的な型は高さ32の全二分木になる. 
`type 'a p = 'a * 'a`とすると
`x0: 'a -> 'a p`
`x1: 'a -> 'a p p`
`x2: 'a -> 'a p p p p` (`p` が$2^2$個)
`x3: 'a -> 'a p p p p p p p p p` (`p` が$2^3$個)
`x4: 'a -> 'a p ... p` (`p` が$2^4$個)
`x5: 'a -> 'a p ... p` (`p` が$2^5$個)
`x5 (fun x-> x): ('a->'a) p ... p` (`'a->'a`が$2^{2^5} = 2^{32}$個)

### hatten3

### References
[1]: [Resource Aware Programming Languages Lectures 5 and 6: Type Inference
, Jan Hoffmann September 29, 2020](https://www.cs.cmu.edu/~janh/courses/ra20/assets/pdf/lect03.pdf)