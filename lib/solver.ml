open Logic
open Z3
module H = Hashtbl

exception Constraint_not_closed of string

(*
  To check a constraint c = forall x. p => c' where there may be many nested forall implications:
  1. Make all forall binders unique in c
  2. Because all binders are unique, we can move all the forall quantifiers to the top
  3. Now c = forall x0, x1, ..., xn . p => c'
  4. It suffices to check that there are no satisfying assignments of ~ (p => c')
  NOTE: Assume that c is closed under Γ, well-formed/ well-sorted, with respect to logical predicates *)
let check ?(dbg = false) ?(fs = []) (c : constraint_) =
  let ctx = mk_context [] in
  (* m_var keeps track of mapping between (our) variables and z3 variables *)
  let m_var : (var, Expr.expr) H.t = H.create 10 in
  (* m_sort keeps track of data type sorts *)
  let m_sort : (var, Sort.sort) H.t = H.create 10 in
  (* m_fun keeps track of uninterpreted functions *)
  let m_fun : (var, FuncDecl.func_decl) H.t = H.create 10 in
  let quant_counter = ref 0 in
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
  let add_sort (s : sort) =
    match s with
    | S_TyCtor tc ->
        if not (H.mem m_sort tc) then
          H.add m_sort tc (Sort.mk_uninterpreted_s ctx tc)
    | _ -> ()
  in
  let translate_sort (s : sort) =
    match s with
    | S_Int -> Arithmetic.Integer.mk_sort ctx
    | S_Bool -> Boolean.mk_sort ctx
    | S_TyCtor tc ->
        add_sort s;
        H.find m_sort tc
  in
  let add_var (v : var) (s : sort) =
    (* Either we haven't seen v yet, in which case create a new z3 variable and update the map, or there already is z3 representation, in which case do nothing *)
    match H.find_opt m_var v with
    | None -> (
        match s with
        | S_Int -> H.add m_var v (Arithmetic.Integer.mk_const_s ctx v)
        | S_Bool -> H.add m_var v (Boolean.mk_const_s ctx v)
        | S_TyCtor tc ->
            add_sort s;
            H.add m_var v (Expr.mk_const_s ctx v (H.find m_sort tc)))
    | _ -> ()
  in
  let add_fun ((f, params, ret, _) : uninterp_fun) =
    let param_sorts = List.map translate_sort params in
    let ret_sort = translate_sort ret in
    let fdecl = FuncDecl.mk_fresh_func_decl ctx f param_sorts ret_sort in
    H.add m_fun f fdecl
  in
  let build_expr (c : constraint_) =
    let rec b_exp_p (p : pred) =
      match p with
      | P_Var v -> H.find m_var v
      | P_True -> Boolean.mk_true ctx
      | P_False -> Boolean.mk_false ctx
      | P_Int i -> Arithmetic.Integer.mk_numeral_i ctx i
      | P_Op (o, p1, p2) -> (op_to_z3_op o) (b_exp_p p1) (b_exp_p p2)
      | P_Disj (p1, p2) -> Boolean.mk_or ctx [ b_exp_p p1; b_exp_p p2 ]
      | P_Conj (p1, p2) -> Boolean.mk_and ctx [ b_exp_p p1; b_exp_p p2 ]
      | P_Neg p' -> Boolean.mk_not ctx (b_exp_p p')
      | P_FunApp (f, args) ->
          let fdecl = H.find m_fun f in
          let e_args = List.map b_exp_p args in
          FuncDecl.apply fdecl e_args
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
  let _ = List.map add_fun fs in
  let fv = Logic.collect_fv_c c in
  if fv != [] then raise (Constraint_not_closed (String.concat "," fv))
  else
    let c' = uniqueify_binders c in
    let c'' =
      List.fold_left
        (fun c (_, _, _, f_cstr) ->
          Option.fold ~none:c
            ~some:(fun f_cstr ->
              match f_cstr with
              | Logic.C_Implication (x, s, p, _) ->
                  let i = !quant_counter in
                  let x' = x ^ "_quant_" ^ string_of_int i in
                  quant_counter := i + 1;
                  add_var x' s;
                  let p' = Logic.substitute_pred x x' p in
                  let cc = strengthen_sort_constraint c s x' p' in
                  cc
              | _ -> c)
            f_cstr)
        c' fs
    in
    let formula = Boolean.mk_not ctx (build_expr c'') in
    let solver = Solver.mk_solver ctx None in
    match Solver.check solver [ formula ] with
    | Solver.SATISFIABLE ->
       if dbg then
          Solver.get_model solver
          |> Option.fold ~none:() ~some:(fun m ->
                 print_endline @@ Model.to_string m);
        false
    | Solver.UNSATISFIABLE -> true
    | Solver.UNKNOWN -> failwith "Z3 returned unknown"
