(* open Pp *)

(* Subtyping tests *)
let%test "Fail subtyping: int <: (int -> int)" =
  let t = Parse.string_to_type "int{v: False}" in
  let t' = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

let%test "Fail subtyping: int :> (int -> int)" =
  let t' = Parse.string_to_type "int{v: True}" in
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

let%test "Successfull subtyping: (int -> int) <: (int -> int)" =
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  Solver.check (Typecheck.sub t t)

let%test "Fail subtyping: int :> bool)" =
  let t' = Parse.string_to_type "bool{v: True}" in
  let t = Parse.string_to_type "int{v: True}" in
  try Solver.check (Typecheck.sub t t')
  with Typecheck.Subtyping_error _ -> true

(* Type checking tests *)
let%test "Integer identity function typechecks" =
  let e = Parse.string_to_expr "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "x:int{v: True} -> int{v: True}" in
  let c = Typecheck.check g e t in
  (* dbg @@ pp_constraint c; *)
  Solver.check c

let%test "Fail when trying to check an abstraction against an int" =
  let e = Parse.string_to_expr "(fn x. x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: True}" in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Invalid_arrow_type _ -> true

let%test "Constant 0 checks" =
  let e = Parse.string_to_expr "0" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: False}" in
  not (Solver.check (Typecheck.check g e t))

let%test "Constant 0 refined precicely" =
  let e = Parse.string_to_expr "0" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v = 0}" in
  Solver.check (Typecheck.check g e t)

let%test "Constant 5 refined gt 4" =
  let e = Parse.string_to_expr "5" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v > 4}" in
  Solver.check (Typecheck.check g e t)

let%test "Constant 5 refined lt 10" =
  let e = Parse.string_to_expr "5" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{v: v < 10}" in
  Solver.check (Typecheck.check g e t)

let%test "Var checks with same type as in environment" =
  let e = Parse.string_to_expr "let y = 1 in y" in
  let t = Parse.string_to_type "int{v: True}" in
  (* let g = Typecheck.E_Cons ("y", t, Typecheck.E_Empty) in *)
  let g = Typecheck.E_Empty in
  Solver.check (Typecheck.check g e t)

let%test "Var checks with subtype of type in environment" =
  let e = Parse.string_to_expr "x" in
  let s = Parse.string_to_type "int{v: v = 42}" in
  let g = Typecheck.E_Cons ("x", s, Typecheck.E_Empty) in
  let t = Parse.string_to_type "int{v: True}" in
  Solver.check (Typecheck.check g e t)

let%test "Var doesn't check with supertype of type in environment" =
  let e = Parse.string_to_expr "x" in
  let s = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("x", s, Typecheck.E_Empty) in
  let t = Parse.string_to_type "int{v: v = 42}" in
  not (Solver.check (Typecheck.check g e t))

let%test "Fun app without annotation doesn't check" =
  let e = Parse.string_to_expr "(fn x. x) x" in
  let t = Parse.string_to_type "int{v: 42}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Fun app first exp not a function type" =
  let e = Parse.string_to_expr "x x" in
  let t = Parse.string_to_type "int{v: 42}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Var not in Γ doesnt check" =
  let e = Parse.string_to_expr "y" in
  let t = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("x", t, Typecheck.E_Empty) in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Fun app with annotation checks" =
  let e = Parse.string_to_expr "(fn x. x):y:int{v: True} -> int{v: True} z" in
  let t = Parse.string_to_type "int{v: v = 42}" in
  let t' = Parse.string_to_type "int{v: True}" in
  let g = Typecheck.E_Cons ("z", t, Typecheck.E_Empty) in
  Solver.check (Typecheck.check g e t')

let%test "Let exp checks (int)" =
  let e = Parse.string_to_expr "let x = 42 in x" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{z: z <= 42}" in
  Solver.check (Typecheck.check g e t)

let%test "Let exp checks (bool)" =
  let e = Parse.string_to_expr "let x = true in (let y = false in x)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "bool{z: z}" in
  Solver.check (Typecheck.check g e t)

let%test "Let rec exp with no recursion checks" =
  let e = Parse.string_to_expr "let rec x = 42 : int{x: x = 42} in x" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  Solver.check (Typecheck.check g e t)

let%test "Let rec exp with recursive definition checks" =
  let e = Parse.string_to_expr "let rec x = x : int{x: x = 42} in x" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  Solver.check (Typecheck.check g e t)

let%test "Regular let exp with recursion fails" =
  let e = Parse.string_to_expr "let x = x : int{x: x = 42} in x" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Let rec exp w/ recursive def. and annotation checks" =
  let e =
    Parse.string_to_expr "let rec x = x : int{x: x = 42} : int{x: x = 42} in x"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  Solver.check (Typecheck.check g e t)

let%test "Let rec exp with recursive fun checks (infinite recursion)" =
  let e =
    Parse.string_to_expr
      "let one = 1 in let rec f = (fn x. f x) : x:int{x: True} -> int{v: v = \
       42} in f one"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  Solver.check (Typecheck.check g e t)

let%test "42 + 10 checks with precice refined type" =
  let e = Parse.string_to_expr "let x = 42 in let y = 10 in add x y" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{z: z = 52}" in
  Solver.check (Typecheck.check g e t)

let%test "If-then-else checks (with path-dependency)" =
  let e = Parse.string_to_expr "let x = true in (if x then 1 else 0)" in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "int{n: n = 1}" in
  let c = Typecheck.check g e t in
  (*  dbg @@ pp_constraint c; *)
  Solver.check c

let%test "And3 function" =
  let e =
    Parse.string_to_expr
      {|
  let conj = ((fn a. (fn b. (if a then b else false))):a:bool{v:True} -> b:bool{v:True} -> bool{v:v=(a&b)}) in
  let conjThree = (((fn a. (fn b. (fn c. (let x = (conj a b) in (conj x c)))))):a:bool{v:True} -> b:bool{v:True} -> c:bool{v:True} -> bool{v:v=(a & b & c)}) in
  let t = true in
  conjThree t t t
    |}
  in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "bool{b: b = True}" in
  Solver.check (Typecheck.check g e t)

let%test "Or function" =
  let e =
    Parse.string_to_expr
      {|
  let disj = ((fn a. (fn b. (if a then true else b))):a:bool{v:True} -> b:bool{v:True} -> bool{v:v=(a|b)}) in
  let f = false in
  disj f f
      |}
  in
  let g = Typecheck.E_Empty in
  let t = Parse.string_to_type "bool{b: b = False}" in
  Solver.check (Typecheck.check g e t)

(* ------------------------ Data Types ------------------------------- *)

let ext_env g (x, t) = Typecheck.E_Cons (x, t, g)
let rgb_sort = Logic.S_TyCtor "rgb"
let isgreen : Logic.uninterp_fun = ("isgreen", [ rgb_sort ], Logic.S_Bool)

let rgb_env =
  let tc =
    Parse.string_to_ty_ctor
      {|
 type rgb =
 | Red => {v: ~ isgreen(v)}
 | Green => {v: isgreen(v)}
 | Blue => {v: ~ isgreen(v)}.
 |}
  in
  Ast.tc_to_tys tc |> List.fold_left ext_env Typecheck.E_Empty

let%test "green is green" =
  let e = Parse.string_to_expr "let x = Green in x" in
  let t = Parse.string_to_type "rgb{v: isgreen(v)}" in
  Solver.check ~fs:[ isgreen ] (Typecheck.check rgb_env e t)

let%test "red is not green" =
  let e = Parse.string_to_expr "let x = Red in x" in
  let t = Parse.string_to_type "rgb{v: isgreen(v)}" in
  not (Solver.check ~fs:[ isgreen ] (Typecheck.check rgb_env e t))

let%test "Switch branch can affect output" =
  let e =
    Parse.string_to_expr
      {|
             let f = (fn x. switch x {Red => false | Green => true | Blue => false}) : x:rgb{v: True } -> bool{b: b=isgreen(x)}
             in let x = Blue in
             f x
             |}
  in
  let t = Parse.string_to_type "bool{b: ~ b}" in
  Solver.check ~fs:[ isgreen ] (Typecheck.check rgb_env e t)

let%test "Typechecking switch expression on variable not in environment fails" =
  let e =
    Parse.string_to_expr
      "switch x {Red => false | Green => true | Blue => false}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try Solver.check ~fs:[ isgreen ] (Typecheck.check rgb_env e t)
  with Typecheck.Switch_error _ -> true

let%test "Typechecking switch expression against non-existent constructor fails"
    =
  let e =
    Parse.string_to_expr
      "let x = Green in switch x {Red => false | Green => true | Blue => false \
       | Yellow => false}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try Solver.check ~fs:[ isgreen ] (Typecheck.check rgb_env e t)
  with Typecheck.Switch_error _ -> true

let list_sort = Logic.S_TyCtor "list"
let len : Logic.uninterp_fun = ("len", [ list_sort ], Logic.S_Int)

let list_tc =
  Parse.string_to_ty_ctor
    {|
 type list =
 | Nil => {v: len(v) = 0 }
 | Cons(x:int{v: True}, xs:list{v: True}) => {v: len(v) = (1 + len(xs))}.
       |}

let doublelist_sort = Logic.S_TyCtor "doublelist"

let doublelist_tc =
  Parse.string_to_ty_ctor
    {|
 type doublelist =
 | DNil
 | DCons(x:int{v: True}, y:int{v: True}, xs:boollist{v: True}).
       |}

let list_env =
  Ast.tc_to_tys list_tc |> List.fold_left ext_env Typecheck.base_env

let list_env' = Ast.tc_to_tys doublelist_tc |> List.fold_left ext_env list_env

let%test "Incorrect constructor pattern in switch expression" =
  let e =
    Parse.string_to_expr
      "let x = Nil in switch x {Nil(x, xs) => true | Cons => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try Solver.check ~fs:[ len ] (Typecheck.check list_env e t)
  with Typecheck.Switch_error _ -> true

let%test "Switch pattern of different data type fails" =
  let e =
    Parse.string_to_expr
      "let x = Nil in switch x {DNil => true | DCons(x, y, xs) => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try Solver.check ~fs:[ len ] (Typecheck.check list_env' e t)
  with Typecheck.Switch_error _ -> true

let%test "Nil has length 0" =
  let e = Parse.string_to_expr "let x = Nil in x" in
  let t = Parse.string_to_type "list{v: len(x) = 0}" in
  Solver.check ~fs:[ len ] (Typecheck.check list_env e t)

let%test "Singleton function outputs list of length 1" =
  let e =
    Parse.string_to_expr
      {|
             let singleton = (fn x. Cons x Nil): x:int{v: True} -> list{v: len(v) = 1}
             in let x = 42 in
             singleton x
              |}
  in
  let t = Parse.string_to_type "list{v: len(v) = 1}" in
  Solver.check ~fs:[ len ] (Typecheck.check list_env e t)

let%test "Safe head positive" =
  let e =
    Parse.string_to_expr
      {|
             let assert = (fn b. 0) : b:bool{b: b} -> int{v: True} in
             let safehead =
             (fn xs.
             switch xs {
             | Cons(hd, tl) => hd
             | Nil => let fls = false in assert fls
             }) : xs:list{v: 0 < len(v)} -> int{v: True}
             in
             let x = 42 in
             let xs = Cons x Nil in
             safehead xs
              |}
  in
  let t = Parse.string_to_type "int{v: True}" in
  Solver.check ~fs:[ len ] (Typecheck.check list_env e t)

let%test "Safe head negative" =
  let e =
    Parse.string_to_expr
      {|
             let assert = (fn b. 0) : b:bool{b: b} -> int{v: True} in
             let safehead =
             (fn xs.
             switch xs {
             | Cons(hd, tl) => hd
             | Nil => let fls = false in assert fls
             }) : xs:list{v: 0 < len(v)} -> int{v: True}
             in
             let xs = Nil in
             safehead xs
              |}
  in
  let t = Parse.string_to_type "int{v: True}" in
  not (Solver.check ~fs:[ len ] (Typecheck.check list_env e t))

let%test "length reflects len" =
  let e =
    Parse.string_to_expr
      {|
             let rec length =
             (fn xs.
             switch xs {
             | Cons(hd, tl) => let lengthtail = length tl in let one = 1 in add lengthtail one
             | Nil => 0
             }) : xs:list{v: True} -> int{v: v = len(xs)} in
             length
              |}
  in
  let t = Parse.string_to_type "xs:list{v: True} -> int{v: v = len(xs)}" in
  Solver.check ~fs:[ len ] (Typecheck.check list_env e t)

let%test "append reflects len" =
  let e =
    Parse.string_to_expr
      {|
             let rec append =
             (fn xs.
               (fn ys.
                 switch xs {
                 | Nil => ys
                 | Cons(hd, tl) => let apptl = append tl ys in Cons hd apptl
                 }
               )
             ) : xs:list{v: True} -> ys:list{v: True} -> list{v: len(v) = len(xs) + len(ys)}
             in true
      |}
  in
  let t = Parse.string_to_type "bool{v: True}" in
  let c = Typecheck.check list_env e t in
  (* dbg @@ pp_constraint c; *)
  Solver.check ~fs:[ len ] c

let inner_sig = "xs:list{v: True} -> int{v: v = (acc + listsum(xs))}"
let middle_sig = Printf.sprintf "acc:int{v: True} -> %s" inner_sig

let outer_sig =
  Printf.sprintf
    "f:acc:int{v: True} -> x:int{v: True} -> int{v: v = (acc + x)} -> %s"
    middle_sig

let sum_specialized_foldl_def =
  Printf.sprintf
    {|
   let rec foldl =
   (fn f. (fn acc. (fn xs.
   switch xs {
   | Nil => acc
   | Cons(hd, tl) => let res = f acc hd in foldl f res tl
   }):%s):%s):%s
   |}
    inner_sig middle_sig outer_sig

let listsum = ("listsum", [ list_sort ], Logic.S_Int)

let list_tc' =
  Parse.string_to_ty_ctor
    {|
     type list =
     | Nil => {v: listsum(v) = 0}
     | Cons(x:int{v: True}, xs:list{v: True}) => {v: listsum(v) = (x + listsum(xs))}.
     |}

let list_env' =
  Ast.tc_to_tys list_tc' |> List.fold_left ext_env Typecheck.base_env

let%test "fold left add" =
  let e =
    Parse.string_to_expr
      (Printf.sprintf
         {|
          %s
          in
          let sum = (fn xs. let zero = 0 in foldl add zero xs) : xs:list{v: True} -> int{v: v = listsum(xs)}
          in sum
          |}
         sum_specialized_foldl_def)
  in
  let t = Parse.string_to_type "xs:list{v: True} -> int{v: v = listsum(xs)}" in
  let c = Typecheck.check list_env' e t in
  Solver.check ~fs:[ listsum ] c
