open Logic
open Z3

(*
  To check a constraint c = forall x. p => c' where there may be many nested forall implications:
  1. Make all forall binders unique in c
  2. Because all binders are unique, we can move all the forall quantifiers to the top
  3. Now c = forall x0, x1, ..., xn . p => c'
  4. It suffices to check that there are no satisfying assignments of ~ (p => c')
  NOTE: Assume that c is closed under Γ, well-formed/ well-sorted, with respect to logical predicates *)
let check (c : constraint_) =
  let ctx = mk_context [] in
  (* m keeps track of mapping between (our) variables and z3 variables *)
  let m : (var, Expr.expr) Hashtbl.t = Hashtbl.create 100 in
  let op_to_z3_op (o : op) =
    match o with
    | O_Add -> fun e1 e2 -> Arithmetic.mk_add ctx [ e1; e2 ]
    | O_Sub -> fun e1 e2 -> Arithmetic.mk_sub ctx [ e1; e2 ]
    | O_Eq -> Boolean.mk_eq ctx
    | O_Lt -> Arithmetic.mk_lt ctx
    | O_Le -> Arithmetic.mk_le ctx
    | O_Gt -> Arithmetic.mk_gt ctx
    | O_Ge -> Arithmetic.mk_ge ctx
  in
  let add_var (v : var) (s : sort) =
    (* Either we haven't seen v yet, in which case create a new z3 variable and update the map, or there already is z3 representation, in which case do nothing *)
    match Hashtbl.find_opt m v with
    | None -> (
        match s with
        | S_Int -> Hashtbl.add m v (Arithmetic.Integer.mk_const_s ctx v)
        | S_Bool -> Hashtbl.add m v (Boolean.mk_const_s ctx v))
    | _ -> ()
  in
  let build_expr (c : constraint_) =
    let rec b_exp_p (p : pred) =
      match p with
      | P_Var v -> Hashtbl.find m v
      | P_True -> Boolean.mk_true ctx
      | P_False -> Boolean.mk_false ctx
      | P_Int i -> Arithmetic.Integer.mk_numeral_i ctx i
      | P_Op (o, p1, p2) -> (op_to_z3_op o) (b_exp_p p1) (b_exp_p p2)
      | P_Disj (p1, p2) -> Boolean.mk_or ctx [ b_exp_p p1; b_exp_p p2 ]
      | P_Conj (p1, p2) -> Boolean.mk_and ctx [ b_exp_p p1; b_exp_p p2 ]
      | P_Neg p' -> Boolean.mk_not ctx (b_exp_p p')
    in
    let rec b_exp_c (c : constraint_) =
      match c with
      | C_Pred p -> b_exp_p p
      | C_Conj (c1, c2) -> Boolean.mk_and ctx [ b_exp_c c1; b_exp_c c2 ]
      | C_Implication (v, s, p, c') ->
          add_var v s;
          Boolean.mk_implies ctx (b_exp_p p) (b_exp_c c')
    in
    b_exp_c c
  in
  let c' = uniqueify_binders c in
  let formula = Boolean.mk_not ctx (build_expr c') in
  let solver = Solver.mk_solver ctx None in
  match Solver.check solver [ formula ] with
  | Solver.SATISFIABLE -> false
  | Solver.UNSATISFIABLE -> true
  | Solver.UNKNOWN -> failwith "Z3 returned unknown"
