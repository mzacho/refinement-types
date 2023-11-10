open Ast
open Logic

(* This file defines data that could be convenient to use in testing/
   during development etc. *)

let t1 = T_Refined (B_Int, "x", P_True)
let e1 = E_Abs ("x", E_Var "x")
