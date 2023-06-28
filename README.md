# ocaml-interpreter
![MIT](https://img.shields.io/badge/License-MIT-red.svg)

A basic interpreter for OCaml subset. Assignment for Functional &amp; Logical Programming at UTokyo, 2023S.

This repo is transferred from the local homework directory.
# How to build
Needs opam [dune](https://github.com/ocaml/dune).
```zsh
$ ls
common       dune-project hatten1      report.md    toi123       toi4
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
`toi123/main.exe` is call-by-value, `toi4/main.exe` is call-by-name, and `hatten1/main.exe` is call-by-need.

# Examples
## `toi123/main.exe` Call-by-value
### list and tuple
```ocaml
$ ./toi123/main.exe
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
### pattern matching
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

#### `reverse`
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
#### `fibonacci` `map` `range`
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
#### `fold_left`
```ocaml
# let rec fold_left f acc xs = match xs with
  | [] -> acc
  | x :: xs' -> fold_left f (f acc x) xs'
  in 
  fold_left (fun acc x -> acc + x) 0 [1; 2; 3; 4; 5];;
- : int = 15
```
#### `concat_map`
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
## `toi4/main.exe` Call-by-name
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
`2+3` here is evaluated twice.

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
`loop ()` here is not evaluated.
### Operations on infinite lists
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

## `hatten1/main.exe` Call-by-need
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
`(2+3)` is evaluated only once.

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
