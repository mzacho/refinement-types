open Ast
open Parse
open Logic

(* let parse_prog s: string = *)
(*   let ast = string_to_program s in *)
(*   pp_program ast *)

(* let parse_type s: string = *)
(*   let ast = string_to_type s in *)
(*   pp_type ast *)

let%test "const" = string_to_program "0" = E_Const 0
let%test "var" = string_to_program "x" = E_Var "x"
let%test "fun abs" = string_to_program "(fn x. x)" = E_Abs ("x", E_Var "x")

let%test "fun abs" =
  string_to_program "(fn x. (fn x. x))" = E_Abs ("x", E_Abs ("x", E_Var "x"))

let%test "fun app" = string_to_program "0 x" = E_App (E_Const 0, "x")
let%test "fun app" = string_to_program "x x" = E_App (E_Var "x", "x")

let%test "fun app" =
  string_to_program "(fn x. x) x" = E_App (E_Abs ("x", E_Var "x"), "x")

let x' = "x"
let x = E_Var x'
let o = E_Const 0
let%test "let expression" = string_to_program "let x = 0 in x" = E_Let (x', o, x)
let y' = "y"
let y = E_Var y'
let l = E_Const 1

let%test "let expression" =
  string_to_program "let x = (fn y. 0) in 1" = E_Let (x', E_Abs (y', o), l)

let%test "let expression nested" =
  string_to_program "let x = 0 in let x = (fn y. 0) in 1"
  = E_Let (x', o, E_Let (x', E_Abs (y', o), l))

(* Refined types *)

let int' = T_Refined (B_Int, "x", P_True)
let%test _ = string_to_type "int{x: True}" = int'
let arrow = T_Arrow ("x", int', int')
let%test "function type" = string_to_type "x:int{x: True}->int{x: True}" = arrow

let%test "annotated expression" =
  string_to_program "0:int{x: True}" = E_Ann (o, int')

let%test "annotated exprs with arrow type" =
  string_to_program "(fn x. x):x:int{x: True}->int{x: True}"
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
