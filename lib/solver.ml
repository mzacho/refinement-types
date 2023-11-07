type var = string

type op =
  | O_add
  (* todo *)

type sort =
  | S_Int

type pred =
  | P_Var of var
  | P_True
  | P_False
  | P_Int of int
  | P_Op of op * pred * pred
  | P_disj of pred * pred
  | P_conj of pred * pred
  | P_neg of pred
  (* | P_Fun of var *)

type constraint_ =
  | C_Pred of pred
  | C_Implication of (var * sort * pred * constraint_)

let check (cs: constraint_) =
  let _ = cs in true
