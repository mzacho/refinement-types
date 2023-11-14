open Logic
open Solver

let x = "x"
let y = "y"
let z = "z"
let zero = P_Int 0
let one = P_Int 1

(* Simple tests *)
let%test "Check true" =
  let c_true = C_Pred P_True in
  check c_true

let%test "Check ~(false)" =
  let c_false = C_Pred P_False in
  not (check c_false)

let%test "Check 1 = 1" =
  let c = C_Pred (P_Op (O_Eq, one, one)) in
  check c

let%test "Check ~(1 = 0)" =
  let c = C_Pred (P_Neg (P_Op (O_Eq, one, zero))) in
  check c

(* Implications *)

(* Ex falso: forall x:int. false => 1 = 0 *)
let%test "Check forall x:int. false => 1 = 0" =
  let c0 = C_Pred (P_Op (O_Eq, one, zero)) in
  let c1 = (x, S_Int, P_False) ==> c0 in
  check c1

(* Transitivity of integer equality:
   forall x:int. true => forall y:int. x = y => forall z:int. y = z => x = z
*)
let%test "Check forall x:int. true => forall y:int. x = y => forall z:int. y = \
          z => x = z" =
  let c0 = C_Pred (P_Op (O_Eq, P_Var x, P_Var z)) in
  let c1 = (z, S_Int, P_Op (O_Eq, P_Var y, P_Var z)) ==> c0 in
  let c2 = (y, S_Int, P_Op (O_Eq, P_Var x, P_Var y)) ==> c1 in
  let c3 = (x, S_Int, P_True) ==> c2 in
  check c3

(* Increment implies strictly less than:
   forall x:int. true => forall y:int. y = x + 1 => x < y
*)
let%test "Check forall x:int. true => forall y:int. y = x + 1 => x < y" =
  let c0 = C_Pred (P_Op (O_Lt, P_Var x, P_Var y)) in
  let c1 =
    (y, S_Int, P_Op (O_Eq, P_Var y, P_Op (O_Add, P_Var x, one))) ==> c0
  in
  let c2 = (x, S_Int, P_True) ==> c1 in
  check c2

(* Forall binders are respected:
   forall x:int. x = 0 => forall x:int. x = 1 => x = 1 *)
let%test "Check forall x:int. x = 0 => forall x:int. x = 1 => x = 1" =
  let c0 = C_Pred (P_Op (O_Eq, P_Var x, one)) in
  let c1 = (x, S_Int, P_Op (O_Eq, P_Var x, one)) ==> c0 in
  let c2 = (x, S_Int, P_Op (O_Eq, P_Var x, zero)) ==> c1 in
  check c2
