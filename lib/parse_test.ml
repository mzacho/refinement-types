open Ast
open Parse
open Logic

(* let parse_prog s: string = *)
(*   let ast = string_to_program s in *)
(*   pp_program ast *)

(* let parse_type s: string = *)
(*   let ast = string_to_type s in *)
(*   pp_type ast *)

(* consts *)
let%test _ = string_to_program "0" = E_Const 0

(* vars *)
let%test _ = string_to_program "x" = E_Var "x"

(* fun abs *)
let%test _ = string_to_program "(fn x. x)" = E_Abs ("x", E_Var "x")

(* fun abs *)
let%test _ =
  string_to_program "(fn x. (fn x. x))" = E_Abs ("x", E_Abs ("x", E_Var "x"))

(* fun app *)
let%test _ = string_to_program "0 x" = E_App (E_Const 0, "x")

(* fun app *)
let%test _ = string_to_program "x x" = E_App (E_Var "x", "x")

(* fun app *)
let%test _ =
  string_to_program "(fn x. x) x" = E_App (E_Abs ("x", E_Var "x"), "x")

let x' = "x"
let x = E_Var x'
let o = E_Const 0

(* let expressions *)
let%test _ = string_to_program "let x = 0 in x" = E_Let (x', o, x)
let y' = "y"
let y = E_Var y'
let l = E_Const 1

(* let expressions *)
let%test _ =
  string_to_program "let x = (fn y. 0) in 1" = E_Let (x', E_Abs (y', o), l)

(* let expressions nested *)
let%test _ =
  string_to_program "let x = 0 in let x = (fn y. 0) in 1"
  = E_Let (x', o, E_Let (x', E_Abs (y', o), l))

(* Refined types *)

let int' = T_Refined (B_Int, "x", P_True)
let%test _ = string_to_type "int{x: True}" = int'

(* Function types *)
let arrow = T_Arrow ("x", int', int')
let%test _ = string_to_type "x:int{x: True}->int{x: True}" = arrow

(* annotated exprs *)
let%test _ = string_to_program "0:int{x: True}" = E_Ann (o, int')

(* annotated exprs with arrow type *)
let%test _ =
  string_to_program "(fn x. x):x:int{x: True}->int{x: True}"
  = E_Ann (E_Abs (x', x), arrow)

(* logic predicates *)

let t = P_True
let f = P_False

(* conjunction *)
let%test _ =
  string_to_type "int{x: False & True}" = T_Refined (B_Int, x', P_Conj (f, t))

(* disjunction *)
let%test _ =
  string_to_type "int{x: False | True}" = T_Refined (B_Int, x', P_Disj (f, t))

(* natural numbers: todo - ints *)
let%test _ = string_to_type "int{x: 42}" = T_Refined (B_Int, x', P_Int 42)

(* negation *)
let%test _ =
  string_to_type "int{x: ~ 42}" = T_Refined (B_Int, x', P_Neg (P_Int 42))

(* todo: P_Op *)
