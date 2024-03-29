open Logic

let x = "x"
let y = "y"
let z = "z"

(* Predicate substitution tests *)

(* Simple tests *)
let%test "true[x := y] = true" = P_True = substitute_pred x y P_True
let%test "false[x := y] = false" = P_False = substitute_pred x y P_False
let%test "42[x := y] = 42" = P_Int 42 = substitute_pred x y (P_Int 42)
let%test "x[x := y] = y" = P_Var y = substitute_pred x y (P_Var x)
let%test "z[x := y] = z" = P_Var z = substitute_pred x y (P_Var z)

(* (x + z)[x := y] = y + z *)
let%test "(x + z)[x := y] = y + z" =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Op (O_Add, P_Var y, p2) = substitute_pred x y (P_Op (O_Add, p1, p2))

(* (x \/ z)[x := y] = y \/ z *)
let%test "(x \\/ z)[x := y] = y \\/ z" =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Disj (P_Var y, p2) = substitute_pred x y (P_Disj (p1, p2))

(* (x /\ z)[x := y] = y /\ z *)
let%test "(x /\\ z)[x := y] = y /\\ z" =
  let p1 = P_Var x in
  let p2 = P_Var z in
  P_Conj (P_Var y, p2) = substitute_pred x y (P_Conj (p1, p2))

(* (~ x)[x := y] = (~ y) *)
let%test "(~ x)[x := y] = ~ y" =
  P_Neg (P_Var y) = substitute_pred x y (P_Neg (P_Var x))

(* Constraint substitution *)

let%test "x[x := y] = y (constraint)" =
  C_Pred (P_Var y) = substitute_constraint (C_Pred (P_Var x)) x y

(* Replace in forall: (forall x:int . y => true)[y := z] = forall x:int . z => true *)
let%test "(forall x:int . y => true)[y := z] = forall x:int . z => true" =
  let c = (x, S_Int, P_Var y) ==> C_Pred P_True in
  let expected = (x, S_Int, P_Var z) ==> C_Pred P_True in
  let actual = substitute_constraint c y z in
  expected = actual

(* Avoid capture: (forall x:int . x => true)[x := y] = forall x:int . x => true *)
let%test "(forall x:int . x => true)[x := y] = forall x:int . x => true" =
  let c = (x, S_Int, P_Var x) ==> C_Pred P_True in
  let expected = c in
  let actual = substitute_constraint c x y in
  expected = actual

(* Substitution is propagated: (forall x:int . x => y)[y := z] = forall x:int . x => z *)
let%test "(forall x:int . x => y)[y := z] = forall x:int . x => z" =
  let c = (x, S_Int, P_Var x) ==> C_Pred (P_Var y) in
  let expected = (x, S_Int, P_Var x) ==> C_Pred (P_Var z) in
  let actual = substitute_constraint c y z in
  expected = actual

(* Substitution in conjunction of constraints:
   (x /\ (forall x:int . x => y))[x := y] = y /\ (forall x:int . x => y)
*)
let%test "(x /\\ (forall x:int . x => y))[x := y] = y /\\ (forall x:int . x => \
          y)" =
  let c = C_Conj (C_Pred (P_Var x), (x, S_Int, P_Var x) ==> C_Pred (P_Var y)) in
  let expected =
    C_Conj (C_Pred (P_Var y), (x, S_Int, P_Var x) ==> C_Pred (P_Var y))
  in
  let actual = substitute_constraint c x y in
  expected = actual

(* Make forall binders unique *)
let%test "Quantified variables are made unique: Nested forall-implication" =
  let c = (x, S_Int, P_Var x) ==> ((x, S_Int, P_Var x) ==> C_Pred P_True) in
  match uniqueify_binders c with
  | C_Implication
      (x1, S_Int, P_Var x2, C_Implication (x3, S_Int, P_Var x4, C_Pred P_True))
    ->
      x1 = x2 && (not (x1 = x3)) && x3 = x4
  | _ -> false

(* Make forall binders unique conjunction *)
let%test "Quantified variables are made unique: Conjunction" =
  let c =
    C_Conj
      ( (x, S_Int, P_Var x) ==> C_Pred P_True,
        (x, S_Int, P_Var x) ==> C_Pred P_True )
  in
  match uniqueify_binders c with
  | C_Conj
      ( C_Implication (x1, S_Int, P_Var x2, C_Pred P_True),
        C_Implication (x3, S_Int, P_Var x4, C_Pred P_True) ) ->
      x1 = x2 && (not (x1 = x3)) && x3 = x4
  | _ -> false
