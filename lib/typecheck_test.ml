(* open Pp *)
(* open Ast *)

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

(* Predicate sort *)
let%test "Correct boolean sort" =
  let t = Parse.string_to_type "int{x: ((x + 2) >= 0) & (~ (True = False))}" in
  match t with
  | T_Refined (_, _, p) -> (
      match Typecheck.sort_of [] [ ("x", Logic.S_Int) ] p with
      | Some Logic.S_Bool -> true
      | _ -> false)
  | _ -> true

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

let%test "Regular let exp with recursion fails" =
  let e = Parse.string_to_expr "let x = x : int{x: x = 42} in x" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  try Solver.check (Typecheck.check g e t)
  with Typecheck.Synthesis_error _ -> true

let%test "Let rec exp with recursive fun doesn't check (infinite recursion)" =
  let e =
    Parse.string_to_expr
      "let one = 1 in let rec f = (fn x. f x) : x:int{x: True} -> int{v: v = \
       42} / x in f one"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 42}" in
  not (Solver.check (Typecheck.check g e t))

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

let%test "Typechecking under a data environment with type constructors with \
          clashing names fails" =
  let tc1 = Parse.string_to_ty_ctor "type Foo = Bar." in
  let tc2 = Parse.string_to_ty_ctor "type Foo = Baz." in
  let denv = Typecheck.build_data_env [ tc1; tc2 ] in
  let e = Parse.string_to_expr "let x = Foo in switch x {Baz => true}" in
  let t = Parse.string_to_type "bool{b: True}" in
  let g = Typecheck.E_Empty in
  try Solver.check (Typecheck.check ~denv g e t)
  with Typecheck.Data_env_illformed_error _ -> true

let%test "Typechecking under a data environment with constructors (of same \
          type constructor) with clashing names fails" =
  let tc = Parse.string_to_ty_ctor "type Foo = Bar | Bar." in
  let denv = Typecheck.build_data_env [ tc ] in
  let e = Parse.string_to_expr "let x = Foo in switch x {Bar => true}" in
  let t = Parse.string_to_type "bool{b: True}" in
  let g = Typecheck.E_Empty in
  try Solver.check (Typecheck.check ~denv g e t)
  with Typecheck.Data_env_illformed_error _ -> true

let%test "Typechecking under a data environment with constructors (of \
          different type constructors) with clashing names fails" =
  let tc1 = Parse.string_to_ty_ctor "type Foo = Baz." in
  let tc2 = Parse.string_to_ty_ctor "type Bar = Baz." in
  let denv = Typecheck.build_data_env [ tc1; tc2 ] in
  let e = Parse.string_to_expr "let x = Foo in switch x {Baz => true}" in
  let t = Parse.string_to_type "bool{b: True}" in
  let g = Typecheck.E_Empty in
  try Solver.check (Typecheck.check ~denv g e t)
  with Typecheck.Data_env_illformed_error _ -> true

let rgb_sort = Logic.S_TyCtor "rgb"
let isgreen : Logic.uninterp_fun = ("isgreen", [ rgb_sort ], Logic.S_Bool, None)

let rgb_data_env =
  let tc =
    Parse.string_to_ty_ctor
      {|
 type rgb =
 | Red => {v: ~ isgreen(v)}
 | Green => {v: isgreen(v)}
 | Blue => {v: ~ isgreen(v)}.
 |}
  in
  Typecheck.build_data_env [ tc ]

let%test "green is green" =
  let e = Parse.string_to_expr "let x = Green in x" in
  let t = Parse.string_to_type "rgb{v: isgreen(v)}" in
  Solver.check ~fs:[ isgreen ]
    (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t)

let%test "red is not green" =
  let e = Parse.string_to_expr "let x = Red in x" in
  let t = Parse.string_to_type "rgb{v: isgreen(v)}" in
  not
    (Solver.check ~fs:[ isgreen ]
       (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t))

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
  Solver.check ~fs:[ isgreen ]
    (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t)

let%test "Typechecking switch expression on variable not in environment fails" =
  let e =
    Parse.string_to_expr
      "switch x {Red => false | Green => true | Blue => false}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ isgreen ]
      (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t)
  with Typecheck.Switch_error _ -> true

let%test "Typechecking non-exhaustive switch expression fails" =
  let e =
    Parse.string_to_expr
      "let x = Green in switch x {Red => false | Green => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ isgreen ]
      (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t)
  with Typecheck.Switch_error _ -> true

let%test "Typechecking switch expression against non-existent constructor fails"
    =
  let e =
    Parse.string_to_expr
      "let x = Green in switch x {Red => false | Green => true | Blue => false \
       | Yellow => false}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ isgreen ]
      (Typecheck.check ~denv:rgb_data_env Typecheck.E_Empty e t)
  with Typecheck.Switch_error _ -> true

open Logic

let list_sort = Logic.S_TyCtor "list"

let len : Logic.uninterp_fun =
  ( "len",
    [ list_sort ],
    S_Int,
    Some
      (("l", list_sort, P_Op (O_Le, P_Int 0, P_FunApp ("len", [ P_Var "l" ])))
      ==> C_Pred P_True) )

let list_tc =
  Parse.string_to_ty_ctor
    {|
 type list =
 | Nil => {v: len(v) = 0 }
 | Cons(x:int{v: True}, xs:list{v: True}) => {v: len(v) = 1 + len(xs)}.
       |}

let doublelist_sort = Logic.S_TyCtor "doublelist"

let doublelist_tc =
  Parse.string_to_ty_ctor
    {|
 type doublelist =
 | DNil
 | DCons(x:int{v: True}, y:int{v: True}, xs:doublelist{v: True}).
       |}

let list_data_env = Typecheck.build_data_env [ list_tc ]
let list_data_env' = Typecheck.build_data_env [ list_tc; doublelist_tc ]

let%test "Incorrect constructor pattern in switch expression" =
  let e =
    Parse.string_to_expr
      "let x = Nil in switch x {Nil(x, xs) => true | Cons => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)
  with Typecheck.Switch_error _ -> true

let%test "tail of non-empty list has a length strictly less than the list" =
  let e =
    Parse.string_to_expr "(fn xs. switch xs {Nil => Nil | Cons(y, ys) => ys})"
  in
  let t =
    Parse.string_to_type
      "xs:list{v: len(v) > 0} -> list{v: len(v) >= 0 & len(v) < len(xs)}"
  in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  Solver.check ~dbg:true ~fs:[ len ] c

let%test "Typechecking switch expression on variable fails when alternatives \
          are not constructors of the variable's type" =
  let e =
    Parse.string_to_expr
      "let x = Nil in switch x {DNil => true | DCons(x, y, xs) => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env' Typecheck.base_env e t)
  with Typecheck.Switch_error _ -> true

let%test "Typechecking let expression that binds a variable with the same name \
          as a constructor fails" =
  let e = Parse.string_to_expr "let Nil = 0 in true" in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)
  with Typecheck.Bind_error _ -> true

let%test "Typechecking let-rec expression that binds a variable with the same \
          name as a constructor fails" =
  let e =
    Parse.string_to_expr
      "let rec Nil = (fn x. 0) : x:int{v: True} -> int{v: True} / x in true"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)
  with Typecheck.Bind_error _ -> true

let%test "Typechecking switch on variable that's not a data type fails" =
  let e =
    Parse.string_to_expr
      "let x = 42 in switch x {Nil => true | Cons(x, xs) => true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)
  with Typecheck.Switch_error _ -> true

let%test "Typechecking switch on variable of non-value type (partially applied \
          constructor) fails" =
  let e =
    Parse.string_to_expr
      "let x = 42 in let y = Cons x in switch y {Nil => true | Cons(x, xs) => \
       true}"
  in
  let t = Parse.string_to_type "bool{b: True}" in
  try
    Solver.check ~fs:[ len ]
      (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)
  with Typecheck.Switch_error _ -> true

let%test "Nil has length 0" =
  let e = Parse.string_to_expr "let x = Nil in x" in
  let t = Parse.string_to_type "list{v: len(x) = 0}" in
  Solver.check ~fs:[ len ]
    (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)

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
  Solver.check ~fs:[ len ]
    (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)

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
  Solver.check ~fs:[ len ]
    (Typecheck.check ~denv:list_data_env Typecheck.base_env e t)

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
  not
    (Solver.check ~fs:[ len ]
       (Typecheck.check ~denv:list_data_env Typecheck.base_env e t))

let%test "length reflects len" =
  let e =
    Parse.string_to_expr
      {|
             let rec length =
             (fn xs.
               switch xs {
               | Cons(hd, tl) => let lengthtail = length tl in let one = 1 in add lengthtail one
               | Nil => 0
               }) : xs:list{v: True} -> int{v: v = len(xs)} / len(xs) in
             length
              |}
  in
  let t = Parse.string_to_type "xs:list{v: True} -> int{v: v = len(xs)}" in
  Solver.check ~fs:[ len ]
    (Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t)

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
             ) : xs:list{v: True} -> ys:list{v: True} -> list{v: len(v) = len(xs) + len(ys)} / len(xs)
             in true
      |}
  in
  let t = Parse.string_to_type "bool{v: True}" in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  (* dbg @@ pp_constraint c; *)
  Solver.check ~fs:[ len ] c

let inner_sig = "xs:list{v: True} -> int{v: v = (acc + listsum(xs))}"
let middle_sig = Printf.sprintf "acc:int{v: True} -> %s" inner_sig

let outer_sig =
  Printf.sprintf
    "f:acc:int{v: True} -> x:int{v: True} -> int{v: v = (x + acc)} -> %s"
    middle_sig

let sum_specialized_foldl_def =
  Printf.sprintf
    {|
   let rec foldl =
   (fn f. (fn acc. (fn xs.
   switch xs {
   | Nil => acc
   | Cons(hd, tl) => let res = f hd acc in foldl f res tl
   }))) :%s / len(xs)
   |}
    outer_sig

let listsum = ("listsum", [ list_sort ], Logic.S_Int, None)

let list_tc' =
  Parse.string_to_ty_ctor
    {|
     type list =
     | Nil => {v: (len(v) = 0) & (listsum(v) = 0)}
     | Cons(x:int{v: True}, xs:list{v: True}) => {v: (listsum(v) = (x + listsum(xs))) & (len(v) = (1 + len(xs)))}.
     |}

let list_data_env' = Typecheck.build_data_env [ list_tc' ]

let%test "fold left add" =
  let e =
    Parse.string_to_expr
      (Printf.sprintf
         {|
          %s
          in
          let sum = (fn xs. let zero = 0 in foldl add zero xs): xs:list{v: True} -> int{v: v = listsum(xs)}
          in
          sum
          |}
         sum_specialized_foldl_def)
  in
  let t = Parse.string_to_type "xs:list{v: True} -> int{v: v = listsum(xs)}" in
  let c =
    Typecheck.check ~fs:[ listsum; len ] ~denv:list_data_env' Typecheck.base_env
      e t
  in
  Solver.check ~fs:[ listsum; len ] c

(* ------------------------ termination ------------------------------- *)

let%test "constant fun terminates" =
  let e =
    Parse.string_to_expr
      "let zero = 0 in let rec f = (fn x. 42)\n\
      \   : acc:int{v: True} -> int{v: True} / acc\n\
      \  in f zero"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  Solver.check c

let%test "rec sub one until 0 terminates" =
  let e =
    Parse.string_to_expr
      "let zero = 0 in let one = 1 in let rec f =\n\
      \          (fn x. let b = (lt x) one in\n\
      \                 if b then 0 else\n\
      \                 let newx = (sub x) one in f newx)\n\
      \         : x:int{v: v>=0} -> int{v: True} / x\n\
      \       in\n\
      \         let ten = 10 in f ten"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

let%test "constant curried fun terminates" =
  let e =
    Parse.string_to_expr
      "let zero = 0 in let rec f = (fn a. (fn b. 42))\n\
      \   : x:int{v: True} -> y:int{v: True} -> int{v: True} / x\n\
      \  in (f zero) zero"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  Solver.check c

let%test "constant curried fun terminates (inner metric)" =
  let e =
    Parse.string_to_expr
      {|
       let zero = 0 in let rec f =
           (fn a. (fn b. 42))
           : x:int{v: True} -> y:int{v: True} -> int{v: True} / y
       in (f zero) zero
       |}
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  (* let _ = Pp.dbg @@ Pp.pp_constraint c in *)
  Solver.check c

let%test "curried rec sub 1 until 0 terminates" =
  let e =
    Parse.string_to_expr
      {|
      let zero = 0 in let one = 1 in let rec f =
             (fn x. (fn y. let b = (lt x) one in
                       if b then 0 else
                       let newx = (sub x) one in (f newx) one))
         : x:int{v: v>=0} -> y:int{v: True} -> int{v: True} / x
       in (f zero) zero
     |}
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  (* let _ = Pp.dbg @@ Pp.pp_constraint c in *)
  Solver.check c

let%test "sum of nats terminates" =
  let e =
    Parse.string_to_expr
      "let one = 1 in\n\
      \         let rec sum =\n\
      \           (fn x.\n\
      \             (let b = (lt x) one in\n\
      \               if b then 0 else\n\
      \                 let y = (sub x) one in\n\
      \                 let z = sum y in\n\
      \                   (add z) one))\n\
      \         : x:int{v:True} -> int{v: True} / x\n\
      \       in\n\
      \       let a = 10 in sum a"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  Solver.check c

let%test "sumT: recursion on multiple parameters terminates" =
  let e =
    Parse.string_to_expr
      "let zero = 0 in let one = 1 in let ten = 10 in\n\
      \         let rec sumT =\n\
      \           (fn total.\n\
      \             (fn x. let y = (lt x) one in\n\
      \               if y then total else\n\
      \                 let newx     = (sub x) one in\n\
      \                 let newtotal = (add total) x in\n\
      \                   (sumT newtotal) newx))\n\
      \           : total:int{v: True} -> x:int{v: True} -> int{v: True} / x\n\
      \       in (sumT zero) ten"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

let%test "metric has to be decreasing" =
  let e =
    Parse.string_to_expr
      "let rec f = (fn x. f x) : x:int{v:True} -> int{v:True} / 4 in 0"
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false g e t in
  not @@ Solver.check c

(*
let%test "metric has to be of int sort" =
  let e = Parse.string_to_expr "let rec f = (fn x. f x) : x:int{v:True} -> int{v:True} / (4 >= 3) in 0" in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false g e t in
  not @@ Solver.check c *)

let%test "range terminates: metrics can be decreasing expressions" =
  let e =
    Parse.string_to_expr
      {|
      let one = 1 in let rec range =
          (fn i.
            (fn j. let b = (lt i) j in
              if b
              then
                let newi = (add i) one in
                let tl = (range newi) j in (Cons i) tl
              else Nil))
          : i:int{v: True} -> j:int{v: True} -> list{v: True} / j - i
       in
       let x = 12 in
       let y = 42 in (range x) y
     |}
  in
  let t = Parse.string_to_type "list{v: True}" in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  Solver.check ~fs:[ len ] c

let%test "range terminates (negative): when changing the\n\
         \ recursive call to range i+1 j+1 then range loops\n\
         \ infinitely" =
  let e =
    Parse.string_to_expr
      {|
      let one = 1 in let rec range =
          (fn i.
            (fn j. let b = (lt i) j in
              if b
              then
                let newi = (add i) one in
                let newj = (add j) one in
                let tl = (range newi) newj in (Cons i) tl
              else Nil))
          : i:int{v: True} -> j:int{v: True} -> list{v: True} / j - i
       in
       let x = 12 in
       let y = 42 in (range x) y
     |}
  in
  let t = Parse.string_to_type "list{v: True}" in
  let c = Typecheck.check ~denv:list_data_env Typecheck.base_env e t in
  not (Solver.check ~fs:[ len ] c)

let%test "ackermann terminates: lexicographic metrics" =
  let e =
    Parse.string_to_expr
      {|
        let zero = 0 in let one = 1 in
        let rec ack =
        (fn m. (fn n.
          let b = (eq m) zero in
          if b then (add n) one
          else let newm = (sub m) one in
               let b = (eq n) zero in
               if b then (ack newm) one
               else let newn = (sub n) one in
                    let ackres = (ack m) newn in
                    (ack newm) ackres))
        : m:int{v:v>=0} -> n:int{v:v>=0} -> int{v:v>=0} / m, n
        in
        let x = 42 in
        let y = 1337 in (ack x) y
        |}
  in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false Typecheck.base_env e t in
  Solver.check c

let%test "ackermann terminates (negative): when changing\n\
         \ the recursive call to (ack m) n then ackermann\n\
         \ loops infinitely" =
  let e =
    Parse.string_to_expr
      {|
        let zero = 0 in let one = 1 in
        let rec ack =
        (fn m. (fn n.
          let b = (eq m) zero in
          if b then (add n) one
          else let newm = (sub m) one in
               let b = (eq n) zero in
               if b then (ack newm) one
               else let newn = (sub n) one in
                    let ackres = (ack m) n in
                    (ack newm) ackres))
        : m:int{v:v>=0} -> n:int{v:v>=0} -> int{v:v>=0} / m, n
        in
        let x = 42 in
        let y = 1337 in (ack x) y
        |}
  in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check Typecheck.base_env e t in
  not (Solver.check c)

let%test "braid" =
  let e =
    Parse.string_to_expr
      {|
       let rec braid =
       (fn xs. (fn ys.
       switch xs {
       | Nil => ys
       | Cons(x, zs) => let tl = braid ys zs in Cons x tl
       })) : xs:list{v: True} -> ys:list{v: True} -> list{v: True} / len(xs) + len(ys)
       in
       braid
       |}
  in
  let t =
    Parse.string_to_type "xs:list{v: True} -> ys:list{v: True} -> list{v: True}"
  in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  Solver.check ~fs:[ len ] c

let%test "Bad append (wrong implementation)" =
  let e =
    Parse.string_to_expr
      {|
       let rec append =
       (fn xs. (fn ys.
       switch xs {
       | Nil => ys
       | Cons(hd, tl) => let rest = append xs ys in Cons hd rest
       })) : xs:list{v: True} -> ys:list{v: True} -> list{v: True} / len(xs)
       in
       append
       |}
  in
  let t =
    Parse.string_to_type "xs:list{v: True} -> ys:list{v: True} -> list{v: True}"
  in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  not @@ Solver.check ~fs:[ len ] c

let%test "Bad sum (wrong implementation)" =
  let e =
    Parse.string_to_expr
      {|
       let zero = 0 in
       let one = 1 in
       let rec sum =
       (fn n.
       let b = eq n zero in
       if b then 0 else
       let newn = sub n one in
       let res = sum newn in
       add n res) : n:int{v: True} -> int{v: True} / n in
       0
       |}
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  not @@ Solver.check c

let%test "Bad sumT (wrong termination metric)" =
  let e =
    Parse.string_to_expr
      {|
       let zero = 0 in let one = 1 in let ten = 10 in
       let rec sumT =
       (fn total. (fn x.
       let y = (lt x) one in
       if y then total else
       let newx = (sub x) one in
       let newtotal = (add total) x in
       (sumT newtotal) newx))
       : total:int{v: True} -> x:int{v: True} -> int{v: True} / total
       in
       sumT zero ten
       |}
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check ~debug:false g e t in
  not @@ Solver.check c

let%test "Bad range (wrong implementation)" =
  let e =
    Parse.string_to_expr
      {|
      let one = 1 in let rec range =
          (fn i.
            (fn j. let b = eq i j in
              if b
              then
                let newi = (add i) one in
                let tl = (range newi) j in (Cons i) tl
              else Nil))
          : i:int{v: True} -> j:int{v: True} -> list{v: True} / j - i
       in
       let x = 12 in
       let y = 42 in (range x) y
     |}
  in
  let t = Parse.string_to_type "list{v: True}" in
  let c =
    Typecheck.check ~fs:[ len ] ~denv:list_data_env Typecheck.base_env e t
  in
  not @@ Solver.check ~fs:[ len ] c

(***** PROOFING SIMPLE LEMMAS ***)

let%test "proof: i=2 -> j=3 -> i+j=5" =
  let e =
    Parse.string_to_expr
      {| let two = 2 in
        let three = 3 in
        let five = 5 in

        let rec x = (fn i. (fn j. add i j)
        ) : i:int{i:i=2} -> j:int{j:j=3} -> int{v:v=5} / 42

        in 42
     |}
  in
  let g = Typecheck.base_env in
  let t = Parse.string_to_type "int{v: True}" in
  let c = Typecheck.check g e t in
  (* Pp.dbg @@ Pp.pp_constraint c; *)
  Solver.check c

let sum : Logic.uninterp_fun = ("sum", [ Logic.S_Int ], S_Int, None)

let%test "proof: sum 2 = 3" =
  let e =
    Parse.string_to_expr
      {|
       let zero = 0 in
       let t = sum zero in
       let one = 1 in
       let tt = sum one in
       let two = 2 in
       let ttt = sum two in
       ttt
      |}
  in
  let sum_def =
    ( "sum",
      Parse.string_to_type
        "n:int{v: 0 <= v} -> int{v: v = sum(n) & ((~(n=0) | v=0) & ((n=0) | (v \
         = n + sum(n-1))))}" )
  in
  let g = Typecheck.( >: ) sum_def Typecheck.base_env in
  let t = Parse.string_to_type "int{v: v = 3}" in
  let c = Typecheck.check g e t in
  Solver.check c ~dbg:true ~fs:[ sum ]

let%test "gauss proof: 2 * sum n = n * (n+1)" =
  let e =
    Parse.string_to_expr
      {|
      let rec sumTheorem =
        (fn n.
        let zero = 0 in
        let one = 1 in

        let b = eq n zero in
        if b
        then
          (let t = sum zero in t)
        else
          (
          let nmo = sub n one in
          let npo = add n one in

          let t = sumTheorem nmo in

          let tt = sum n in
          let ttt = sum nmo in

          0
          )
      ) : n:int{n: n >= 0} -> int{v: 2 * sum(n) = n*(n+1)} / n in
      sumTheorem
      |}
  in
  let sum_def =
    ( "sum",
      Parse.string_to_type
        "n:int{v: 0 <= v} -> int{v: v = sum(n) & ((~(n=0) | v=0) & ((n=0) | (v \
         = n + sum(n-1))))}" )
  in
  let g = Typecheck.( >: ) sum_def Typecheck.base_env in
  let t =
    Parse.string_to_type "n:int{n: n>=0} -> int{v: 2 * sum(n) = n * (n+1)}"
  in
  let c = Typecheck.check g e t in
  Solver.check c ~dbg:true ~fs:[ sum ]
