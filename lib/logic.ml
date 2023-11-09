type var = string
type op = O_add
(* todo *)

type sort = S_Int

type pred =
  | P_Var of var
  | P_True
  | P_False
  | P_Int of int
  | P_Op of op * pred * pred
  | P_Disj of pred * pred
  | P_Conj of pred * pred
  | P_Neg of pred
(* | P_Fun of var *)

type constraint_ =
  | C_Pred of pred
  | C_Implication of (var * sort * pred * constraint_)
