open Logic

let x = "x"
let y = "y"
let z = "z"

(* Predicate substitution tests *)

(* Simple tests *)
let%test _ = P_True = substitute_pred P_True x y
let%test _ = P_False = substitute_pred P_False x y
let%test _ = P_Int 42 = substitute_pred (P_Int 42) x y
let%test _ = P_Var y = substitute_pred (P_Var x) x y

(* (x + z)[x := y] = y + z *)
let%test _ =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Op (O_add, P_Var y, p2) = substitute_pred (P_Op (O_add, p1, p2)) x y

(* (x \/ z)[x := y] = y \/ z *)
let%test _ =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Disj (P_Var y, p2) = substitute_pred (P_Disj (p1, p2)) x y

(* (x /\ z)[x := y] = y /\ z *)
let%test _ =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Conj (P_Var y, p2) = substitute_pred (P_Conj (p1, p2)) x y

(* (~ x)[x := y] = (~ y) *)
let%test _ = P_Neg (P_Var y) = substitute_pred (P_Neg (P_Var x)) x y

(* Constraint substitution *)

let%test _ = C_Pred (P_Var y) = substitute_constraint (C_Pred (P_Var x)) x y

(* Replace in forall: (forall x:int . y => true)[y := z] = forall x:int . z => true *)
let%test _ =
  let c = C_Implication (x, S_Int, P_Var y, C_Pred P_True) in
  let expected = C_Implication (x, S_Int, P_Var z, C_Pred P_True) in
  let actual = substitute_constraint c y z in
  expected = actual

(* Avoid capture: (forall x:int . x => true)[x := y] = forall x:int . x => true *)
let%test _ =
  let c = C_Implication (x, S_Int, P_Var x, C_Pred P_True) in
  let expected = c in
  let actual = substitute_constraint c x y in
  expected = actual

(* Substitution is propagated: (forall x:int . x => y)[y := z] = forall x:int . x => z *)
let%test _ =
  let c = C_Implication (x, S_Int, P_Var x, C_Pred (P_Var y)) in
  let expected = C_Implication (x, S_Int, P_Var x, C_Pred (P_Var z)) in
  let actual = substitute_constraint c y z in
  expected = actual

(* Substitution in conjunction of constraints:
   (x /\ (forall x:int . x => y))[x := y] = y /\ (forall x:int . x => y)
*)
let%test _ =
  let c =
    C_Conj
      (C_Pred (P_Var x), C_Implication (x, S_Int, P_Var x, C_Pred (P_Var y)))
  in
  let expected =
    C_Conj
      (C_Pred (P_Var y), C_Implication (x, S_Int, P_Var x, C_Pred (P_Var y)))
  in
  let actual = substitute_constraint c x y in
  expected = actual
