open Ast
open Parse
open Logic

(* let parse_prog s: string = *)
(*   let ast = string_to_expr s in *)
(*   pp_program ast *)

(* let parse_type s: string = *)
(*   let ast = string_to_type s in *)
(*   pp_type ast *)

let%test "false" = string_to_expr "false" = E_False
let%test "const" = string_to_expr "0" = E_Const 0
let%test "var" = string_to_expr "x" = E_Var "x"
let%test "fun abs" = string_to_expr "(fn x. x)" = E_Abs ("x", E_Var "x")

let%test "fun abs" =
  string_to_expr "(fn x. (fn x. x))" = E_Abs ("x", E_Abs ("x", E_Var "x"))

let%test "fun app" = string_to_expr "0 x" = E_App (E_Const 0, "x")
let%test "fun app" = string_to_expr "x x" = E_App (E_Var "x", "x")

let%test "fun app" =
  string_to_expr "(fn x. x) x" = E_App (E_Abs ("x", E_Var "x"), "x")

let x' = "x"
let x = E_Var x'
let o = E_Const 0

let%test "let expression" = string_to_expr "let x = 0 in x" = E_Let (x', o, x)

let y' = "y"
let y = E_Var y'
let l = E_Const 1

let%test "let expression" =
  string_to_expr "let x = (fn y. 0) in 1" = E_Let (x', E_Abs (y', o), l)

let%test "let expression nested" =
  string_to_expr "let x = 0 in let x = (fn y. 0) in 1"
  = E_Let (x', o, E_Let (x', E_Abs (y', o), l))

let%test "plus x y" =
  string_to_expr "let x = 43 in let y = 10 in add x y"
  = E_Let
      ( x',
        E_Const 43,
        E_Let (y', E_Const 10, E_App (E_App (E_Var "add", "x"), "y")) )

let int' = T_Refined (B_Int, "x", P_True)
let arrow = T_Arrow ("x", int', int')

let%test "let rec expression" =
  string_to_expr
    "let rec f = (fn x. x) : x:int{x: True} -> int{x: True} / x in 1"
  = E_RLet ("f", E_Abs (x', x), arrow, [ P_Var x' ], l)

let%test "let rec expression annotated" =
  string_to_expr
    "let rec f = (fn x. x) : x:int{x: True} -> int{x: True} : x:int{x: True} \
     -> int{x: True} / x in 1"
  = E_RLet ("f", E_Ann (E_Abs (x', x), arrow), arrow, [ P_Var x' ], l)

(* let%test "let rec decreasing" = *)
(*   string_to_program "let zero = 0 in let one = 1 in let rec f = (fn x. let b = (lt x) zero in if b then 0 else let y = (sub x) one in f y) : x:int{x:True}->int{y.True} / x in 42" = E_Let ("zero", E_Const 0 , E_RLet ("f", E_Ann (E_Abs (x', E_Let ( "b", E_App ( E_App ( E_Var "lt", x'), "zero"), E_Const 0)), arrow), arrow, [ P_Var x' ], l)) *)

(* Refined types *)

let%test _ = string_to_type "int{x: True}" = int'
let%test "function type" = string_to_type "x:int{x: True}->int{x: True}" = arrow

let%test "annotated expression" =
  string_to_expr "0:int{x: True}" = E_Ann (o, int')

let%test "annotated exprs with arrow type" =
  string_to_expr "(fn x. x):x:int{x: True}->int{x: True}"
  = E_Ann (E_Abs (x', x), arrow)

(* logic predicates *)

let t = P_True
let f = P_False

let%test "conjunction" =
  string_to_type "int{x: False & True}" = T_Refined (B_Int, x', P_Conj (f, t))

let%test "disjunction" =
  string_to_type "int{x: False | True}" = T_Refined (B_Int, x', P_Disj (f, t))

let%test "nat type predicate" =
  string_to_type "int{x: x >= 0}"
  = T_Refined (B_Int, x', P_Op (O_Ge, P_Var x', P_Int 0))

let%test "negation" =
  string_to_type "int{x: ~ False}" = T_Refined (B_Int, x', P_Neg P_False)

let%test "int refined to: 0 = x" =
  string_to_type "int{x: x = 0}"
  = T_Refined (B_Int, x', P_Op (O_Eq, P_Var x', P_Int 0))

let%test "int refined to: 0 != x" =
  string_to_type "int{x: x != 0}"
  = T_Refined (B_Int, x', P_Neg (P_Op (O_Eq, P_Var x', P_Int 0)))

let%test "int refined to: 1 <= x < 4" =
  string_to_type "int{x: (1 <= x) & (x < 4)}"
  = T_Refined
      ( B_Int,
        x',
        P_Conj (P_Op (O_Le, P_Int 1, P_Var x'), P_Op (O_Lt, P_Var x', P_Int 4))
      )

let%test "int refined to: 10 > (x - 1) & ((x + 1) >= 4" =
  string_to_type "int{x: (10 > (x - 1)) & ((x + 1) >= 4)}"
  = T_Refined
      ( B_Int,
        x',
        P_Conj
          ( P_Op (O_Gt, P_Int 10, P_Op (O_Sub, P_Var x', P_Int 1)),
            P_Op (O_Ge, P_Op (O_Add, P_Var x', P_Int 1), P_Int 4) ) )

let%test "precedence of >=, =, &" =
  string_to_type "int{x: x >= 3 & x = 3}"
  = T_Refined
      ( B_Int,
        x',
        P_Conj (P_Op (O_Ge, P_Var x', P_Int 3), P_Op (O_Eq, P_Var x', P_Int 3))
      )

let%test "curried fun type" =
  string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x+y)}"
  = T_Arrow
      ( "x",
        T_Refined (B_Int, "v", t),
        T_Arrow
          ( "y",
            T_Refined (B_Int, "v", t),
            T_Refined
              ( B_Int,
                "z",
                P_Op (O_Eq, P_Var "z", P_Op (O_Add, P_Var x', P_Var y')) ) ) )

let%test "intlist type constructor" =
  let tc =
    string_to_ty_ctor
      {|
       type intlist =
       | Nil
       | Cons(x:int{v: True}, xs:intlist{v: True}).
       |}
  in
  let dc1 = ("Nil", [], None) in
  let dc2 =
    ( "Cons",
      [
        ("x", T_Refined (B_Int, "v", t));
        ("xs", T_Refined (B_TyCtor "intlist", "v", t));
      ],
      None )
  in
  tc = ("intlist", [ dc1; dc2 ])

let%test "switch expression" =
  let e =
    string_to_expr
      {|
       switch x {
       | Nil => true
       | Cons(x, xs) => false
       }
       |}
  in
  e
  = E_Switch
      ("x", [ Alt ("Nil", [], E_True); Alt ("Cons", [ "x"; "xs" ], E_False) ])

let%test "true" = Parse.string_to_expr "true" = E_True
let%test "false" = Parse.string_to_expr "false" = E_False
(* fun abs *)
let%test "x y" = Parse.string_to_expr "x y" = E_App (E_Var "x", "y")

let%test "let x = true in f x " =
  Parse.string_to_expr "let x = true in f x"
  = E_Let ("x", E_True, E_App (E_Var "f", "x"))

let%test "true" = Parse.string_to_expr "true" = E_True
let%test "false" = Parse.string_to_expr "false" = E_False
(* fun abs *)
let%test "x y" = Parse.string_to_expr "x y" = E_App (E_Var "x", "y")

let%test "let x = true in f x " =
  Parse.string_to_expr "let x = true in f x"
  = E_Let ("x", E_True, E_App (E_Var "f", "x"))
