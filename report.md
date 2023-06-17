### ビルド方法
```zsh
$ cd 09-231017
$ ls
common       dune-project hatten1      report.md    toi123       toi4

$ ls toi123/*.exe toi4/*.exe hatten1/*.exe
zsh: no matches found: toi123/*.exe

$ dune build
File "common/dune", line 10, characters 0-26:
10 | (menhir
11 |  (modules parser))
Error: No rule found for common/parser.mly
File "common/dune", line 7, characters 0-27:
7 | (ocamllex
8 |  (modules lexer))
Error: No rule found for common/lexer.mll

$ ls toi123/*.exe toi4/*.exe hatten1/*.exe
hatten1/main.exe toi123/main.exe  toi4/main.exe
```
### toi1

#### `toi23/expr.ml`
新たに
```ocaml
type expr = 
  ...
  | `ETuple of expr list
  | `EList of expr list
  ...
```
を追加する。
ここで、与えられた資料からの変更は主に以下3点である.
1. `ENil` -> `EList([])`
2. `ECons(a, b)` -> `EBinaryOp("::", a, b)`
3. `EPair(a, b)` -> `ETuple([a;b])`
4. 拡張表現`a1, a2, ..., an` -> `ETuple([a1;a2;...;an])`

#### `toi23/parser.mly`
また、OCamlではtupleをカッコを省略して書けるが、それを模倣するためにペア(tuple)のルールを
```ocaml
%token COMMA ","
%nonassoc NOCOMMA 
%nonassoc COMMA
expr:
  | tuple_excluded_expr %prec NOCOMMA { $1 }
  | tuple_expr { $1 }
;
%inline tuple_expr:
  | tuple_excluded_expr "," tuple_excluded_expr_list { `ETuple($1::$3) }
;

tuple_excluded_expr_list:
  | tuple_excluded_expr %prec NOCOMMA { [$1] }
  | tuple_excluded_expr "," tuple_excluded_expr_list { $1::$3 }
;

%inline tuple_excluded_expr:
  | ...
;

```
のところに移動させた.

また、リストのリテラルの構文もサポートした.
```oacaml
%token SEMI ";"
atomic_expr:
  ...
  | "["; es=semi_separated_exprs; "]" { `EList(es) }
  ...
;
semi_separated_exprs:
  | e=expr { [e] }
  | e=expr SEMI {[e]}
  | e=expr SEMI es=semi_separated_exprs { e :: es }
;
```
#### `toi23/value.ml`
`list`と`tuple`を追加した。
```ocaml
type value =
  ...
  | VList of value list
  | VTuple of value list
  ...
```
`::`をサポートするための組込み関数を追加した.
```ocaml
(* exception TypeError of string *)
(* 本当に発生する場合はbugである *)
let builtins : (string * value) list =
  let wrapper2 op f =
    (op, VBuiltinFun (op, fun x -> VBuiltinFun (op ^ "'", fun y -> f (x, y))))
  in
  let sv = string_of_value in
  [
  ...
    wrapper2 "::" (function
      | x, VList xs -> VList (x :: xs)
      | x, y -> raise (TypeError (sv x ^ " :: " ^ sv y)));
  ...
  ]
```

#### `toi23/eval.ml`
`EList`, `ETuple`を評価するコードを追加した
`EList`と`ETuple`の各要素を順次に評価するだけである.
```ocaml
let rec eval_expr (env : value option ref Env.t) (e : expr) : value =
  ...
  | `ETuple es ->
      let vs = List.map (eval_expr env) es in
      VTuple vs
  | `EList es ->
      let vs = List.map (eval_expr env) es in
      VList vs
  ...
```


#### 実行例
```ocaml
# 1, 2;;
- : int * int = (1, 2)

# 1, 2, 3;;
- : int * int * int = (1, 2, 3)

# true, true, (true, true, false);;
- : bool * bool * (bool * bool * bool) = (true, true, (true, true, false))

# [], [];;
- : '6 list * '7 list = ([], [])

# [1;2;3;4;5]=[1;2;3;4;5];;
- : bool = true

# [1;2;3;];;
- : int list = [1; 2; 3]

# [true;false];;
- : bool list = [true; false]

# 1::2::3::4::[];;
- : int list = [1; 2; 3; 4]

# let a = (1, 2) in
let b = (true, false) in
let c = (3, 4, 5) in
let d = ((1, 2), (3, 4)) in
let e = ((1, true), (false, 2)) in
(a, b, c, d, e);;
- : (int * int) * (bool * bool) * (int * int * int) * ((int * int) * (int * int)) * 
((int * bool) * (bool * int)) = 
((1, 2), (true, false), (3, 4, 5), ((1, 2), (3, 4)), ((1, true), (false, 2)))

# let list1 = 1 :: 2 :: 3 :: [];;
val list1: int list = [1; 2; 3]

# let list2 = true :: false :: [];;
val list2: bool list = [true; false]

# let list3 = (1, 2) :: (3, 4) :: [];;
val list3: (int * int) list = [(1, 2); (3, 4)]

# let list4 = [1; 2] :: [3; 4] :: [];;
val list4: int list list = [[1; 2]; [3; 4]]

# (list1, list2, list3, list4);;
- : int list * bool list * (int * int) list * int list list = ([1; 2; 3], [true; false], [(1, 2); (3, 4)], [[1; 2]; [3; 4]])
```

### toi2

#### `toi23/pattern.ml`
パターンの定義は
```ocaml
type pattern =
  | PInt of int
  | PBool of bool
  | PVar of string
  | PCon of string * pattern list
```
である。
ここで`PCon(con, ps)`は型コンストラクタ`con`で引数のパターンが`ps`というパターンを表す。例えば、
|パターン|表示|
|:--:|--|
|`[]`              |`PCon("[]", [])`               |
|`p1::p2`          |`PCon("::', [p1; p2])`         |
|`p1, p2, ..., pn` |`PCon("tuple", [p1;p2;...,pn])`|
#### `toi23/match.ml`
一度照合に成功したら束縛をそのまま返すので
`Monad`的な書き方にした.
```ocaml
exception MatchFailed
let ( let* ) = Option.bind

let find_match p v : (string * value) list option =
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
  Some (List.rev bindings)

```
#### `toi23/expr.ml`
`EMatch`を追加した.
```ocaml
type equation = pattern * t
and t =
  [ `EConstInt of int
  | `EConstBool of bool
  ...
  | `EMatch of t * equation list
  ...
  ]
```
#### `toi23/eval.ml`

```ocaml
let rec eval_expr (env : value option ref Env.t) (e : expr) : value =
  ...
  | `EMatch (e, qs) -> (
      (* qs = [(p[0], e[0]); (p[1], e[1]); ...; (p[n-1], e[n-1]] *)
      let v = eval_expr env e in (* 式`e`を評価し，値`v`を得る *)
      qs
      |> List.fold_left
           (fun acc (p, e) -> (* p[i], e[i] *)
             if Option.is_some acc then acc
             else
               Match.find_match p v
               |> Option.map (fun bindings ->
               (* 照合すれば環境に`bindings`を追加し *)
                      let names, vs = bindings |> List.split in
                      let values =
                        List.rev_map Option.some vs |> List.rev_map ref
                      in
                      let env' = env |> Env.extends names values in
                      (* `e`を評価 *)
                      eval_expr env' e))
           None
      |> function
      | Some v -> v
      | None -> raise Match.MatchFailed)
      (* いずれとも照合しなかったので，例外`Match.MatchFailed`を送出する *)
  ...
```
#### 実行例
##### `length`
```ocaml
# let rec length xs = match xs with
  | [] -> 0
  | x :: xs' -> 1 + length xs';;
val length: '9. '9 list -> int = <fun (xs)>

# length [1; 2; 3; 4; 5];;
- : int = 5

# length [[]; [1]; [1; 2]; [1; 2; 3]];;
- : int = 4
```

##### `reverse`
```ocaml
# let rec reverse xs =
  let rec reverse' acc = function
    | [] -> acc
    | x :: xs' -> reverse' (x :: acc) xs'
  in reverse' [] xs;;
val reverse: '20. '20 list -> '20 list = <fun (xs)>

# reverse [1; 2; 3; 4; 5];;
- : int list = [5; 4; 3; 2; 1]

# reverse [[]; [1]; [1; 2]; [1; 2; 3]];;
- : int list list = [[1; 2; 3]; [1; 2]; [1]; []]
```
##### `fibonacci` `map` `range`
```ocaml
# let rec fibonacci n =
  let rec fib n a b =
    match n with
    | 0 -> a
    | 1 -> b
    | n -> fib (n - 1) b (a + b)
  in fib n 0 1;;
val fibonacci: int -> int = <fun (n)>

# let rec range l r = if l >= r then [] else l::range (l+1) r;;
val range: int -> int -> int list = <fun (l)>

# let rec map f xs = 
    match xs with
    | [] -> []
    | x::xs' -> f x :: map f xs';;
val map: '65 '67. ('65 -> '67) -> '65 list -> '67 list = <fun (f)>

# map fibonacci (range 0 20);;
- : int list = [0; 1; 1; 2; 3; 5; 8; 13; 21; 34; 55; 89; 144; 233; 377; 610; 987; 1597; 2584; 4181]
```
##### `fold_left`
```ocaml
# let rec fold_left f acc xs = match xs with
  | [] -> acc
  | x :: xs' -> fold_left f (f acc x) xs'
  in 
  fold_left (fun acc x -> acc + x) 0 [1; 2; 3; 4; 5];;
- : int = 15
```
##### `concat_map`
```ocaml
# let rec concat_map f xs = match xs with
  | [] -> []
  | x :: xs' -> append (f x) (concat_map f xs')
and append xs ys = match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys;;
val concat_map: '57 '68. ('57 -> '68 list) -> '57 list -> '68 list = <fun (f)>
val append: '68. '68 list -> '68 list -> '68 list = <fun (xs)>

# concat_map (function x, y -> [x * x; y * y]) [(2, 3); (4, 5); (6, 7)];;
- : int list = [4; 9; 16; 25; 36; 49]

# concat_map (function (b1, b2) -> [b1 && b2; b1 || b2]) [(true, true); (true, false); (false, false)];;
- : bool list = [true; true; false; true; false; false]
```


### toi3

#### `toi23/type.ml`
型`Type.t`を簡単化した.
要は型変数以外の型をすべて`型コンストラクタ * ID * 引数のリスト`に統一した.
|型|表示|
|-|-|
|`int`|`TyCon("int", _, [])`|
|`bool` | `TyCon("bool", _, [])`|
|`t1 -> t2`|`TyCon("->", _, [t1; t2])`|
|`t list`|`TyCon("list", _, [t])`|
|`unit`| `TyCon("unit", _, [])` |
| `t1 * t2 * ... tn`| `TyCon("tuple", _, [t1; t2; ...; tn])` |
|`'a`|`TypeVar _`|
```ocaml
type typevar_t = [ `TypeVar of int ]
type t_ = t and t = [ `TyCon of string * int * t list | typevar_t ]

let tycon_func = "->"
let tycon_tuple = "tuple"
let tycon_int = "int"
let tycon_bool = "bool"
let tycon_unit = "unit"
let tycon_list = "list"
```
`hash`型のハッシュ値を計算する関数
```ocaml
let hash t =
  match t with
  | `TyCon (_, i, _) -> (2 * i) + 1
  | `TypeVar i -> 2 * i
```
`equal`型が等しいかどうか判断する関数
```ocmal
let equal a b =
  match (a, b) with
  | `TyCon (_, i, _), `TyCon (_, j, _) -> i = j
  | `TypeVar i, `TypeVar j -> i = j
  | _ -> false
```
`constr`型コンストラクタと引数を与え，ただ一つある型を返す関数
```ocaml
let constr : string -> t list -> [> `TyCon of string * int * t list ]
 =
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
```

組込み型のためのヘルパー関数やコンスタントを定義した.
```ocaml
let ty_int = constr tycon_int []
let ty_bool = constr tycon_bool []
let ty_unit = constr tycon_unit []
let func (a, b) = constr tycon_func [ a; b ]
let ty_list t = constr tycon_list [ t ]
let tuple ts = constr tycon_tuple ts
```
#### `toi23/infer.ml`

```ocaml
let rec infer_expr (schema_env : SchemaEnv.t) e = 
  match e with
  ...
```
まずは式 $e$ の型 $t_e$ と制約 $c_e$ を求める.
```ocaml
  ...
  | `EMatch (e, qs) ->
      let t, c = infer_expr schema_env e in
      let rec map2fold1 f x0 = function
        | [] -> ([], [], x0)
        | x :: xs' ->
            let a1, a2, a3 = f x0 x in
            let a1s, a2s, a3' = map2fold1 f a3 xs' in
            (a1 :: a1s, a2 :: a2s, a3')
      in
```
`map2fold1`という関数は1番目と2番目の引数について`map`し
3番目の引数について`fold_left`する関数である.


```ocaml
      let infer_equation (lhs, rhs) =
        let rec infer_pattern env p : Type.t * constraint_t nlist * Type.t Env.t
            =
          match p with
```
次は各パターンの形によって場合分けする.
```ocaml
          | Pattern.PVar x ->
              let alpha :> Type.t = Type.new_typevar () in
              (alpha, List [], env |> Env.extend x alpha)
          | Pattern.PInt _ -> (Type.ty_int, List [], env)
          | Pattern.PBool _ -> (Type.ty_bool, List [], env)
          | Pattern.PCon ("tuple", ps) ->
              assert (List.length ps > 1);
              let ts, cs, env' = map2fold1 infer_pattern env ps in
              (Type.tuple ts, Nested cs, env')
          | Pattern.PCon ("[]", []) ->
              (Type.ty_list (Type.new_typevar () :> Type.t), List [], env)
          | Pattern.PCon ("::", [ p1; p2 ]) ->
              let t1, c1, env1 = infer_pattern env p1 in
              let t2, c2, env2 = infer_pattern env1 p2 in
              (t2, Nested [ c1; c2; List [ (t2, Type.ty_list t1) ] ], env2)
```
以上は基本的にスライド通りである.
`Nested _`と`List _`に関しては後で説明する.
ここではappendがlazyなリストとして理解して良い.
```ocaml
          | Pattern.PCon (con, ps) ->
              raise (UnknownTypeConstructorError (con, List.length ps))
        in (* end of infer_pattern env p *)
        let t'l, c'l, env'l = infer_pattern Env.empty lhs in
        let g ty =
          generalize (Nested [ c; c'l; List [ (t, t'l) ] ]) schema_env ty
        in
        let schema_env' =
          List.fold_left
            (fun acc (x', t') -> acc |> SchemaEnv.extend x' (g t'))
            schema_env env'l
        in
        let t'r, c'r = infer_expr schema_env' rhs in
        (t'r, Nested [ c'l; List [ (t, t'l) ]; c'r ])
      in (* end of infer_equation (lhs, rhs) *)
```
以上は，ある$i$について
パターンと式の組を$p_i \rightarrow e_i $とすると
$p_i$ の型 $t_i=$`t'l`と制約 $c_i=$`c'l`, および追加される型環境 $\Gamma_i=$`env'l`を求める.

$\Gamma_i$の各束縛 $name \mapsto t_{name}$ について`generalize`を行い, 型スキーマ$s_{name}$を得る.
- $c_e \cup c_i \cup \{t_e = t_i\}$を制約に`generalize`

$name \mapsto s_{name}$をすべて型スキーマ環境$\Delta$($=$`schema_env`)に追加して
$\Delta'=$`schema_env'`を得る.

$\Delta'$の下で $e_i=$`rhs`の型推論を行って$t_i'=$ `t'r`と $c_i'=$`c'r`を得る.
最後に $t_i'$ と $C_i' \left(= c_i \cup \{t_e = t_i\}\cup c_i' \right)$ を返す.

```ocaml
      let t'rs, c'qs = List.map infer_equation qs |> List.split in
      let alpha :> Type.t = Type.new_typevar () in
      ( alpha,
        Nested
          [
            c;
            Nested
              (List.map2
                 (fun t'r c'q -> Nested [ c'q; List [ (alpha, t'r) ] ])
                 t'rs c'qs);
          ] )
```
新たな型変数$\alpha$を導入して, `match`式の型$\alpha$, 制約$c_e \cup \bigcup_{i=1}^n \left[ C_i' \cup \{\alpha = t_i'\} \right]$を返す.

実行例はtoi2を参照してください.
##### `'a nlist`
リストを木構造で保存し，必要な時だけflattenする.
```ocaml
type 'a nlist = List of 'a list | Nested of 'a nlist list

let flatten l =
  let rec flatten' : 'a nlist -> 'a list = function
    | List x -> x
    | Nested xs -> List.concat_map flatten' xs
  in
  flatten' l

let iter f l =
  let rec iter' f l =
    match l with
    | List xs -> List.iter f xs
    | Nested xs -> List.iter (iter' f) xs
  in
  iter' f l
```

### toi4
#### `toi4/value.ml`
`value`の定義を以下のように変える.
```ocaml
type value =
  [ `VInt of int
  | `VBool of bool
  | `VUnit
  | `VTuple of thunk list
  | `VList of thunk list
  | `VCons of thunk * thunk
  | `VFunc of string * Expr.t * thunk option ref Env.t
  | `VBuiltinFun of string * (thunk -> value) ]

and thunk =
  | Thunk of Expr.t * thunk option ref Env.t
  | BuiltinFunction of [ `VBuiltinFun of string * (thunk -> value) ]
```
環境には値ではなくサンクを保存するほか, `VList`と`VTuple`の中にもサンクのリストである必要がある.
組込み関数の引数の型も`value`から`thunk`に変えた.

`List.map`のためにサンクを生成する関数`make_thunk`を定義する.
```ocaml
let make_thunk env e = Thunk (e, env)
```
#### `toi4/eval.ml`
サンクを評価する関数eval_thunkを定義する
```ocaml
let depth = ref 0

let rec eval_thunk (t : thunk) : value =
  depth := !depth + 1;
  (* Printf.printf "--> eval_thunk: %s\n" (Value.string_of_thunk t); *)
  let v =
    match t with
    | Value.Thunk (e, env) ->
        let res = eval_expr env e in
        Printf.printf "%*seval_thunk: %s = %s\n" (!depth * 2) ""
          (Value.string_of_thunk t)
          (Value.string_of_value res);
        res
    | Value.BuiltinFunction f -> (f :> value)
  in
  depth := !depth - 1;
  v


```
`printf`でどのサンクが評価されたかがわかる.
次はeval_exprの実装である．
値呼びに比べて，変更点は主に
`EVar, ECall, ETuple, EList, EMatch, ELet, ELetRec`にある.

```ocaml
and eval_expr (env : thunk option ref Env.t) (e : expr) : value =
  match e with
  ...
```
##### `EVar x`
`x`に対応するサンクを探してそれを評価する.
```ocaml
  ...
  | `EVar x -> (
      try
        match !(Env.lookup x env) with
        | Some thunk -> eval_thunk thunk
        | None -> raise (Transform.InvalidLetRecRhs (`EVar x))
      with Not_found -> raise (Transform.UnboundVariable x))
```
##### `ECall(e1, e2)`
```ocaml
  | `ECall (e1, e2) -> (
      let v1 = eval_expr env e1 in
      match v1 with
      | `VFunc (x, e', oenv) ->
          let r = Value.Thunk (e2, env) |> Option.some |> ref in
          eval_expr (oenv |> Env.extend x r) e'
      | `VBuiltinFun (_, f) -> f (Thunk (e2, env))
      | v -> raise (NotCallable v))
```
- 環境`env`で`e1`を評価し`v1`とする
- サンク `Thunk(e2, env)` を作る
  - `v1`が組み込み関数`VBuiltinFun (_, f)`ならば
    `f (Thunk(e2, env))`を評価する
  - そうでない場合は`v1`が`VFunc (x, e', oenv)`である
  　式eを環境 $\{$`x`$\mapsto$`Thunk(e2, env)`$\}\cup$`env'` の下で評価
##### `ETuple es`または`EList es`
```ocaml
  | `ETuple es ->
      let vs = List.map (Value.make_thunk env) es in
      `VTuple vs
  | `EList es ->
      let vs = List.map (Value.make_thunk env) es in
      `VList vs
```
各要素を現在の環境下でサンクにするだけである.

##### `EMatch`
```ocaml
  | `EMatch (_, _) -> raise (NotImplementedError "`EMatch")
```
##### `ELet((vars, e1s), e2)`
`let vars'1 = e1s'1 and vars'2 = e1s'2 and ... and vars'n = e1s'n in e2`
```ocaml
  | `EFun ...
  | `ELet ((vars, e1s), e2) ->
      (* let v1s = List.map (eval_expr env) e1s in *)
      let env' =
        List.fold_left2
          (fun env0 var e ->
            env0 |> Env.extend var (ref (Some (Value.Thunk (e, env)))))
          env vars e1s
      in
      eval_expr env' e2
```
要は`e1s'i`($i=1, 2, ..., n$)の値を即に評価せずにサンクにして環境に入れるだけである.
##### `ELetRec`
```ocaml
  | `ELetRec ((vars, es), body) ->
      (* let rec vars'1=es'1 and vars'2=es'2 ... and vars'n=es'n in body *)
      let env' =
        List.fold_left
          (fun env0 var -> env0 |> Env.extend var (ref None))
          env vars
      in
      List.iter2
        (fun var rhs ->
          let v = env' |> Env.lookup var in
          assert (Option.is_none !v);
          v := Some (Thunk (rhs, env')))
        vars es;
      eval_expr env' body
  | `EIf ...
```
`ELet`とほぼ同じだが，環境にあらかじめ`ref None`を入れてあげて得た環境の下でサンクを作る.
作り終わったら環境中の束縛を`ref None`から`ref (Some (Thunk _))`に変更する.

##### `::` `fst` `snd` `hd` `tl`

`thunk`は評価が必要なため組込み関数の定義を`value.ml`から`eval.ml`に移した.

```ocaml
let builtins : (string * [> `VBuiltinFun of string * (thunk -> value) ]) list =
  let open Value in
  let wrapper (op: string) f =
    (op, `VBuiltinFun (op, fun thunk -> f (eval_thunk thunk)))
  in
  let wrapper2 op f = ...
  let wrapper2_lazy op f =
    (op, `VBuiltinFun (op, fun x -> `VBuiltinFun (op ^ "'", fun y -> f (x, y))))
  in
  let sv = string_of_value and st = string_of_thunk in 
  [
    ...
    wrapper2_lazy "::" (function
      | x, y -> `VCons (x, y));

    wrapper "fst" (function
      | `VTuple [ x'; _ ] -> eval_thunk x'
      | x -> raise (TypeError ("fst " ^ sv x)));

    wrapper "snd" (function
      | `VTuple [ _; y' ] -> eval_thunk y'
      | x -> raise (TypeError ("snd " ^ sv x)));

    wrapper "hd" (function
      | `VCons (x', _) -> eval_thunk x'
      | `VList (x' :: _) -> eval_thunk x'
      | `VList [] -> raise (Invalid_argument "hd []")
      | x -> raise (TypeError ("hd " ^ sv x)));

    wrapper "tl" (function
      | `VCons (_, xs) -> eval_thunk xs
      | `VList (_ :: xs) -> `VList xs
      | `VList [] -> raise (Invalid_argument "tl []")
      | x -> raise (TypeError ("tl " ^ sv x)));
    ...
  ]
```
実行例
```ocaml
# (fun x -> x * x) (2 + 3);;
        eval_thunk: <thunk 3> = 3
        eval_thunk: <thunk 2> = 2
      eval_thunk: <thunk (+) 2 3> = 5
    eval_thunk: <thunk x> = 5
        eval_thunk: <thunk 3> = 3
        eval_thunk: <thunk 2> = 2
      eval_thunk: <thunk (+) 2 3> = 5
    eval_thunk: <thunk x> = 5
  eval_thunk: <thunk (fun#3 x -> ( * ) x x) ((+) 2 3)> = 25
- : int = 25
```
`2+3`が $2$ 回評価されたことがわかる.

```ocaml
# let x = 2 + 5 in x + x * x;;
          eval_thunk: <thunk 5> = 5
          eval_thunk: <thunk 2> = 2
        eval_thunk: <thunk (+) 2 5> = 7
      eval_thunk: <thunk x> = 7
          eval_thunk: <thunk 5> = 5
          eval_thunk: <thunk 2> = 2
        eval_thunk: <thunk (+) 2 5> = 7
      eval_thunk: <thunk x> = 7
    eval_thunk: <thunk ( * ) x x> = 49
        eval_thunk: <thunk 5> = 5
        eval_thunk: <thunk 2> = 2
      eval_thunk: <thunk (+) 2 5> = 7
    eval_thunk: <thunk x> = 7
  eval_thunk: <thunk let "x" = ((+) 2 5) in ((+) x (( * ) x x))> = 56
- : int = 56

# (fun x -> x + x * x) (2 + 5);;
          eval_thunk: <thunk 5> = 5
          eval_thunk: <thunk 2> = 2
        eval_thunk: <thunk (+) 2 5> = 7
      eval_thunk: <thunk x> = 7
          eval_thunk: <thunk 5> = 5
          eval_thunk: <thunk 2> = 2
        eval_thunk: <thunk (+) 2 5> = 7
      eval_thunk: <thunk x> = 7
    eval_thunk: <thunk ( * ) x x> = 49
        eval_thunk: <thunk 5> = 5
        eval_thunk: <thunk 2> = 2
      eval_thunk: <thunk (+) 2 5> = 7
    eval_thunk: <thunk x> = 7
  eval_thunk: <thunk (fun#2 x -> (+) x (( * ) x x)) ((+) 2 5)> = 56
- : int = 56
```
`loop ()`が評価されていないことがわかる.

##### 無限リストの評価
```ocaml
# let rec range_from x0 = x0 :: range_from (x0 + 1);;
val range_from: int -> int list = <fun (x0)>
# let naturals = range_from 0;;
  eval_thunk: <thunk fun#1 x0 -> (::) x0 (range_from ((+) x0 1))> = <fun (x0)>
val naturals: int list = <thunk x0> :: <thunk range_from ((+) x0 1)>
# hd naturals;;
        eval_thunk: <thunk fun#1 x0 -> (::) x0 (range_from ((+) x0 1))> = <fun (x0)>
      eval_thunk: <thunk range_from 0> = <thunk x0> :: <thunk range_from ((+) x0 1)>
    eval_thunk: <thunk naturals> = <thunk x0> :: <thunk range_from ((+) x0 1)>
      eval_thunk: <thunk 0> = 0
    eval_thunk: <thunk x0> = 0
  eval_thunk: <thunk hd naturals> = 0
- : int = 0
# hd (tl (tl naturals));;
            eval_thunk: <thunk fun#1 x0 -> (::) x0 (range_from ((+) x0 1))> = <fun (x0)>
          eval_thunk: <thunk range_from 0> = <thunk x0> :: <thunk range_from ((+) x0 1)>
        eval_thunk: <thunk naturals> = <thunk x0> :: <thunk range_from ((+) x0 1)>
          eval_thunk: <thunk fun#1 x0 -> (::) x0 (range_from ((+) x0 1))> = <fun (x0)>
        eval_thunk: <thunk range_from ((+) x0 1)> = <thunk x0> :: <thunk range_from ((+) x0 1)>
      eval_thunk: <thunk tl naturals> = <thunk x0> :: <thunk range_from ((+) x0 1)>
        eval_thunk: <thunk fun#1 x0 -> (::) x0 (range_from ((+) x0 1))> = <fun (x0)>
      eval_thunk: <thunk range_from ((+) x0 1)> = <thunk x0> :: <thunk range_from ((+) x0 1)>
    eval_thunk: <thunk tl (tl naturals)> = <thunk x0> :: <thunk range_from ((+) x0 1)>
        eval_thunk: <thunk 1> = 1
            eval_thunk: <thunk 1> = 1
              eval_thunk: <thunk 0> = 0
            eval_thunk: <thunk x0> = 0
          eval_thunk: <thunk (+) x0 1> = 1
        eval_thunk: <thunk x0> = 1
      eval_thunk: <thunk (+) x0 1> = 2
    eval_thunk: <thunk x0> = 2
  eval_thunk: <thunk hd (tl (tl naturals))> = 2
- : int = 2

```

### hatten1
toi4の`eval_thunk`を`eval_dval`に変更する
```ocaml
let depth = ref 0

let rec eval_dval (d : dval) : value =
  depth := !depth + 1;
  let v =
    match d with
    | DThunk (e, env) ->
        let res = eval_expr env e in
        Printf.printf "%*seval_dthunk: %s = %s\n" (!depth * 2) ""
          (Value.string_of_dval d)
          (Value.string_of_value res);
        res
    | DVal v -> v
  in
  depth := !depth - 1;
  v

```
`eval_expr`の`EVar x`のところに
```ocaml
  | `EVar x -> (
      try
        match Env.lookup x env with
        (* | {contents=Some (DVal v)} -> v *)
        | {contents=Some dval} as r -> 
          let v = eval_dval dval in r := Some (DVal v); v
        | {contents=None} -> raise (Transform.InvalidLetRecRhs (`EVar x))
      with Not_found -> raise (Transform.UnboundVariable x))
```
すると

```ocaml
# (fun x -> (fun y -> x * y) x) (2+3);;
          eval_dval: <DThunk 3> = 3
          eval_dval: <DThunk 2> = 2
        eval_dval: <DThunk (+) 2 3> = 5
      eval_dval: <DThunk x> = 5
    eval_dval: <DThunk y> = 5
    eval_dval: <DThunk x> = 5
  eval_dval: <DThunk (fun#2 x -> (fun#1 y -> ( * ) x y) x) ((+) 2 3)> = 25
- : int = 25
```
`(2+3)`の評価は一度だけであることが確認できる.

```ocaml
# let x = 2 + 5 in x + x * x;;
          eval_dval: <DThunk 5> = 5
          eval_dval: <DThunk 2> = 2
        eval_dval: <DThunk (+) 2 5> = 7
      eval_dval: <DThunk x> = 7
      eval_dval: <DThunk x> = 7
    eval_dval: <DThunk ( * ) x x> = 49
    eval_dval: <DThunk x> = 7
  eval_dval: <DThunk let "x" = ((+) 2 5) in ((+) x (( * ) x x))> = 56
- : int = 56

# (fun x -> x + x * x) (2 + 5);;
          eval_dval: <DThunk 5> = 5
          eval_dval: <DThunk 2> = 2
        eval_dval: <DThunk (+) 2 5> = 7
      eval_dval: <DThunk x> = 7
      eval_dval: <DThunk x> = 7
    eval_dval: <DThunk ( * ) x x> = 49
    eval_dval: <DThunk x> = 7
  eval_dval: <DThunk (fun#4 x -> (+) x (( * ) x x)) ((+) 2 5)> = 56
- : int = 56
```

### hatten2
