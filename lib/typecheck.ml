open Pp
module A = Ast
module L = Logic
module R = Result

let debug_indent = ref 0
let r_bind f r x = R.bind r (f x)

let fresh_var_count = ref 0

(* Data environment is a mapping of type constructor names to their (base) type and data constructors *)
type data_env = (A.var * A.ty_ctor) list

(* Lookup the type of a data constructor *)
let lookup_dctor_ty (denv : data_env) (dcname : A.var) : A.ty option =
  List.find_map
    (fun ((_, (_, dctors)) : A.var * A.ty_ctor) -> List.assoc_opt dcname dctors)
    denv

(* Lookup the (base) type and data constructors of a type constructor *)
let lookup_tctor (denv : data_env) (tc : A.var) : A.ty_ctor option =
  List.assoc_opt tc denv

(* Build a data environment from a list of type constructor declarations *)
let build_data_env (tctor_decls : A.ty_ctor_decl list) =
  (* Map a data constructor declaration to a tuple of the name and type of the constructor *)
  let map_dctor_decl (tcname : string)
      ((dcname, binders, refinement) : A.data_ctor_decl) : A.var * A.ty =
    let v, p =
      match refinement with Some (v, p) -> (v, p) | None -> ("v", Logic.P_True)
    in
    (* The type of a data constructor D(x1:t1, ..., xn:tn) for the type constructor C of (base) type C_bty
       can be viewed as a function x1:t1 -> ... -> xn:tn -> C_bty.
       Null-ary constructors (no binders/ arguments) just have type C_bty.
    *)
    let dcty =
      List.fold_right
        (fun (x, s) t -> A.T_Arrow (x, s, t))
        binders
        (A.T_Refined (A.B_TyCtor tcname, v, p))
    in
    (dcname, dcty)
  in
  (* Map a type constructor declaration to a tuple of the name and tuple of base type and list of constructor (name, type) pairs *)
  let map_tctor_decl (denv : data_env) ((tcname, dctors) : A.ty_ctor_decl) :
      (A.var * A.ty_ctor) list =
    (tcname, (A.B_TyCtor tcname, List.map (map_dctor_decl tcname) dctors))
    :: denv
  in
  List.fold_left map_tctor_decl [] tctor_decls

type env = E_Empty | E_Cons of (A.var * A.ty * env)
type logic_env = (L.var * L.sort) list

let rec env_to_list (g : env) : (A.var * A.ty) list=
  match g with E_Empty -> [] | E_Cons (x, t, g') -> (x, t) :: env_to_list g'

let rec denv_to_list (de : data_env) : (A.var * A.ty) list =
  match de with
  | [] -> []
  | (_, ty_ctor)::de' ->
     let (_, dctors) = ty_ctor in
     dctors @ denv_to_list de' (* (name, A.T_Refined (bty, name, L.P_True)) :: *)

(* notation *)
let ( >: ) (v, t) g = E_Cons (v, t, g)
let ( ==> ) x p = L.( ==> ) x p

let base_env =
  ("add", Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x+y)}")
  >: (( "sub",
        Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x-y)}" )
     >: (( "lt",
           Parse.string_to_type
             "x:int{v:True}->y:int{v:True}->bool{z:(~z | (x < y)) & (~(x < y) \
              | z)}" )
         >: (( "ge",
           Parse.string_to_type
             "x:int{v:True}->y:int{v:True}->bool{z:(~z | (x >= y)) & (~(x >= y) \
              | z)}" )
        >: (( "eq",
              Parse.string_to_type
                "x:int{v:True}->y:int{v:True}->bool{z:(~z | (x = y)) & (~(x = \
                 y) | z)}" )
           >: E_Empty))))

exception Synthesis_error of string
exception Subtyping_error of string
exception Invalid_arrow_type of string
exception Invalid_abs_expression of string
exception Switch_error of string
exception Data_env_illformed_error of string
exception Bind_error of string
exception Termination_error of string

(* for easier debugging strip unnecessary trues *)
let rec strip_trues (c : L.constraint_) =
  match c with
  | C_Pred _ -> c
  | C_Conj (C_Pred P_True, b) -> strip_trues b
  | C_Conj (a, C_Pred P_True) -> strip_trues a
  | C_Conj (a, b) -> C_Conj (strip_trues a, strip_trues b)
  | C_Implication (v, s, p, c) -> C_Implication (v, s, p, strip_trues c)

(* Check that:
   1. No two type constructors have the same name
   2. No two data constructors have the same name

   Returns
   - Ok (denv), if denv doesn't violate the above, otherwise
   - Error (e), where e is an exception describing which of the above was violated.
*)
let check_data_env (denv : data_env) =
  let dctor_wellformed (denv : data_env) (dctor : A.var * A.ty)
      (dctors : (A.var * A.ty) list) =
    let dcname, _ = dctor in
    if
      (not (List.for_all (fun (dcname', _) -> dcname <> dcname') dctors))
      || lookup_dctor_ty denv dcname <> None
    then R.error (Data_env_illformed_error "Data constructor name clash")
    else R.ok (dctor :: dctors)
  in
  let tctor_wellformed (tctor : A.var * (A.base_ty * (A.var * A.ty) list)) denv
      =
    let tcname, (_, dctors) = tctor in
    if lookup_tctor denv tcname <> None then
      R.error (Data_env_illformed_error "Type constructor name clash")
    else
      let r =
        List.fold_left (r_bind (dctor_wellformed denv)) (R.ok []) dctors
      in
      R.fold ~ok:(fun _ -> R.ok (tctor :: denv)) ~error:(fun e -> R.error e) r
  in
  List.fold_left (r_bind tctor_wellformed) (R.ok []) denv

let rec lookup (g : env) (v : A.var) : A.ty option =
  match g with
  | E_Empty -> None
  | E_Cons (v', t', g') -> if String.equal v' v then Some t' else lookup g' v

let ty_to_sort (t : A.base_ty) =
  match t with
  | A.B_Int -> L.S_Int
  | A.B_Bool -> L.S_Bool
  | A.B_TyCtor tc -> L.S_TyCtor tc

let implication (x : A.var) (t : A.ty) (c : L.constraint_) : L.constraint_ =
  match t with
  | A.T_Refined (bt, v, p) -> (x, ty_to_sort bt, L.substitute_pred v x p) ==> c
  | _ -> c

let rec implications (xs : (A.var * A.ty) list) (c : L.constraint_) :
    L.constraint_ =
  match xs with
  | [] -> c
  | (x, t) :: xs' -> implications xs' (implication x t c)

let fresh_var () : A.var =
  fresh_var_count := !fresh_var_count + 1;
  "fr" ^ Printf.sprintf "%d" (!fresh_var_count - 1)

(* Computes t[y := z] in a capture avoiding manner, see RTT 3.1 *)
let rec substitute_type (y : A.var) (z : A.var) (t : A.ty) : A.ty =
  match t with
  | T_Refined (b, v, p) ->
     if String.equal v y then t else
       if String.equal v z then
         let fv = fresh_var () in
         T_Refined (b, fv, L.substitute_pred y z @@ L.substitute_pred v fv p)
         else T_Refined (b, v, L.substitute_pred y z p)
  | T_Arrow (v, s, t) ->
      if String.equal v y then T_Arrow (v, substitute_type y z s, t)
      else T_Arrow (v, substitute_type y z s, substitute_type y z t)

let rec sub (g: env) (s : A.ty) (t : A.ty) : L.constraint_ =
  match s with
  | T_Refined (b, v1, p1) -> (
      match t with
      | T_Refined (b', v2, p2) ->
          if not (b = b') then
            raise
              (Subtyping_error
                 ("Refined types have different base types: " ^ pp_type s
                ^ " and " ^ pp_type t))
          else let v = fresh_var() in (v, ty_to_sort b, Logic.substitute_pred v1 v p1) ==> L.C_Pred (L.substitute_pred v2 v p2)
      | T_Arrow _ -> raise (Subtyping_error "Expected refined type"))
  | T_Arrow (x1, s1, t1) -> (
      match t with
      | T_Arrow (x2, s2, t2) ->
          let ci = sub g s2 s1 in
          let co = sub g (substitute_type x1 x2 t1) t2 in
          L.C_Conj (ci, implication x2 s2 co)
      | T_Refined _ -> raise (Subtyping_error "Expected arrow type"))

(* selfification, see Section 4 *)
let self (v : A.var) (t : A.ty) : A.ty =
  match t with
  | T_Refined (b, v', p) ->
      T_Refined (b, v', L.P_Conj (p, L.P_Op (O_Eq, P_Var v, P_Var v')))
  | T_Arrow _ -> t

(* see ENT-EXT *)
let rec close (g : env) (c : L.constraint_) : L.constraint_ =
  match g with
  | E_Cons (x, (T_Refined _ as t), g') ->
      let c' = close g' c in
      if L.occurs_free_c x c then implication x t c' else c'
  | E_Cons (_, _, g') -> close g' c
  | _ -> c

(* Close the constraint with respect to user-defined data types:
   The null-ary data constructors must be quantified over for the constraint to be closed *)
let close_data (denv : data_env) (c : L.constraint_) : L.constraint_ =
  let f (c : L.constraint_) (dcname, dcty) =
    match dcty with A.T_Refined _ -> implication dcname dcty c | _ -> c
  in
  let cls (c : L.constraint_)
      ((_, (_, dctors)) : A.var * (A.base_ty * (A.var * A.ty) list)) =
    List.fold_left f c dctors
  in
  List.fold_left cls c denv

let split_lambdas (e1, t1) : (A.var * A.ty) list * A.expr * A.ty =
  let rec split acc e t =
    match (e, t) with
    | A.E_Abs (_, e), A.T_Arrow (x, s, t) -> split ((x, s) :: acc) e t
    | A.E_Abs _, _ ->
        raise
          (Invalid_abs_expression
             "Expected function type for E_Abs in split_lambdas")
    | eb, tb -> (List.rev acc, eb, tb)
  in
  split [] e1 t1

let rec rename_ty e s m =
  match (e, s) with
  | A.E_Abs (x, e), A.T_Arrow (y, s, t) ->
      let s' = substitute_type y x s in
      let t' = substitute_type y x t in
      let m' = List.map (L.substitute_pred y x) m in
      let t'', m'' = rename_ty e t' m' in
      (A.T_Arrow (x, s', t''), m'')
  | _ -> (s, m)

let rec add_vars (g : env) (ys : (A.var * A.ty) list) : env =
  match ys with [] -> g | (x, t) :: ys' -> (x, t) >: add_vars g ys'

let rec sort_of (fs : L.uninterp_fun list) (g : logic_env) (p : L.pred) =
  match p with
  | L.P_Int _ -> Some L.S_Int
  | L.P_True | L.P_False -> Some L.S_Bool
  | L.P_Conj (p1, p2) | L.P_Disj (p1, p2) -> (
      match (sort_of fs g p1, sort_of fs g p2) with
      | Some L.S_Bool, Some L.S_Bool -> Some L.S_Bool
      | _ -> None)
  | L.P_Neg p ->
      if sort_of fs g p |> ( = ) (Some L.S_Bool) then Some L.S_Bool else None
  | L.P_Op (L.O_Eq, p1, p2) -> (
      let s = sort_of fs g p1 in
      let s' = sort_of fs g p2 in
      match (s, s') with
      | Some (L.S_TyCtor tc), Some (L.S_TyCtor tc') ->
          if tc = tc' then Some (Logic.S_TyCtor tc) else None
      | Some s, Some s' -> if s = s' then Some s else None
      | _ -> None)
  | L.P_Op (L.O_Add, p1, p2) | L.P_Op (L.O_Sub, p1, p2) -> (
      let s = sort_of fs g p1 in
      let s' = sort_of fs g p2 in
      match (s, s') with
      | Some L.S_Int, Some L.S_Int -> Some L.S_Int
      | _ -> None)
  | L.P_Op (L.O_Lt, p1, p2)
  | L.P_Op (L.O_Le, p1, p2)
  | L.P_Op (L.O_Gt, p1, p2)
  | L.P_Op (L.O_Ge, p1, p2) -> (
      let s = sort_of fs g p1 in
      let s' = sort_of fs g p2 in
      match (s, s') with
      | Some L.S_Int, Some L.S_Int -> Some L.S_Bool
      | _ -> None)
  | L.P_Var v -> List.assoc_opt v g
  | L.P_FunApp (f, args) ->
      let _, arg_sorts, out_sort, _ =
        List.find (fun (f', _, _, _) -> f = f') fs
      in
      if
        List.for_all2
          (fun p s ->
            match (sort_of fs g p, s) with
            | Some (L.S_TyCtor tc), L.S_TyCtor tc' -> tc = tc'
            | Some s, s' -> s = s'
            | _ -> false)
          args arg_sorts
      then Some out_sort
      else None

and check_sort (fs : L.uninterp_fun list) (g : logic_env) (p : L.pred)
    (s : L.sort) : bool =
  match p with
  | L.P_Int _ -> s = L.S_Int
  (* check that both predicates are int-sorted *)
  | L.P_Op (O_Add, p1, p2) | L.P_Op (O_Sub, p1, p2) ->
      s = L.S_Int && check_sort fs g p1 L.S_Int && check_sort fs g p2 L.S_Int
  | L.P_Op (O_Le, p1, p2)
  | L.P_Op (O_Ge, p1, p2)
  | L.P_Op (O_Gt, p1, p2)
  | L.P_Op (O_Lt, p1, p2) ->
      s = L.S_Bool && check_sort fs g p1 L.S_Int && check_sort fs g p2 L.S_Int
  | L.P_Op (O_Eq, p1, p2) -> (
      s = L.S_Bool
      &&
      match (sort_of fs g p1, sort_of fs g p2) with
      | Some (L.S_TyCtor tc), Some (L.S_TyCtor tc') -> tc = tc'
      | Some s1, Some s2 -> s1 = s2
      | _ -> false)
  | L.P_Var x -> (
      try
        let _, s' = List.find (fun (y, _) -> String.equal y x) g in
        s' = s
      with Not_found -> false)
  | L.P_FunApp (f, args) ->
      let _, arg_sorts, out_sort, _ =
        List.find (fun (f', _, _, _) -> f = f') fs
      in
      out_sort = s
      && List.for_all2 (fun p s -> check_sort fs g p s) args arg_sorts
  | L.P_True | L.P_False -> s = L.S_Bool
  | L.P_Neg p -> s = L.S_Bool && sort_of fs g p = Some L.S_Bool
  | L.P_Conj (p1, p2) | L.P_Disj (p1, p2) ->
      s = L.S_Bool
      && sort_of fs g p1 = Some L.S_Bool
      && sort_of fs g p2 = Some L.S_Bool

let rec metric_wf' (fs : L.uninterp_fun list) (g : logic_env) (m : A.metric) :
    bool =
  match m with
  | [] -> true
  | p :: m' ->
      (* check that p is int sorted *)
      let b = check_sort fs g p L.S_Int in
      b && metric_wf' fs g m'

let rec env_to_logic_env (g : env) : logic_env =
  match g with
  | E_Empty -> []
  | E_Cons (x, t, g') -> (
      match t with
      | T_Refined (b, _, _) ->
          let b' =
            match b with
            | B_Int -> L.S_Int
            | B_Bool -> L.S_Bool
            | B_TyCtor y -> L.S_TyCtor y
          in
          (x, b') :: env_to_logic_env g'
      | T_Arrow _ -> env_to_logic_env g')

let metric_wf (fs : L.uninterp_fun list) (g : env) (m : A.metric) : bool =
  metric_wf' fs (env_to_logic_env g) m

let rec wfr (m1 : A.metric) (m2 : A.metric) : L.pred =
  match (m1, m2) with
  (* metrics should be non-empty lists - this is guaranteed in programs
     parsed from the concrete syntax, but one can of course violate this
     when writing directly in the AST *)
  | [], [] -> L.P_True
  | [ p ], [ p' ] ->
      L.P_Conj (L.P_Op (L.O_Le, L.P_Int 0, p'), L.P_Op (L.O_Lt, p', p))
  | p :: ps, p' :: ps' ->
      let op1 = L.P_Op (L.O_Le, L.P_Int 0, p') in
      let op2 = L.P_Op (L.O_Lt, p', p) in
      let op3 = L.P_Op (L.O_Eq, p, p') in
      L.P_Conj (op1, L.P_Disj (op2, L.P_Conj (op3, wfr ps ps')))
  | _, _ -> raise (Termination_error "expected metrics of same length in wfr")

let limit_function (fs : L.uninterp_fun list) (g : env) (m : A.metric)
    (ty : A.ty) : A.ty =
  let rec limit' (g : env) (m' : A.metric) (m : A.metric) (ty : A.ty) : A.ty =
    match ty with
    | T_Arrow (x, (A.T_Refined (b, y, p) as s), t)
      when metric_wf fs ((x, s) >: g) m ->
        let x' = fresh_var () in
        (* substitute x' for the binder in the predicate *)
        let p_sub = L.substitute_pred x x' @@ L.substitute_pred y x p in
        (* substitute x' for the binder of the argument in the metric *)
        let m_sub = List.map (L.substitute_pred x x') m in
        (* form the new predicate that the argument must satisfy *)
        let p' = L.P_Conj (p_sub, wfr m' m_sub) in
        (* substitute x' for the binder of the argument in the result type *)
        let t_sub = substitute_type x x' t in
        (* return the limited arrow type *)
        A.T_Arrow (x', A.T_Refined (b, x', p'), t_sub)
    | T_Arrow (x, s, t) ->
        let x' = fresh_var () in
        (* substitute x' for the binder of the argument in the metric *)
        let m_sub = List.map (L.substitute_pred x x') m in
        (* substitute x' for the binder of the argument in the result type *)
        let t_sub = substitute_type x x' t in
        (* limit the result type by calling recursively *)
        let g' = (x', s) >: g in
        let t' = limit' g' m' m_sub t_sub in
        (* substitute x' for the binder of the argument its type
           - not sure if this is correct, since substitute_type is capture avoiding? *)
        let s_sub = substitute_type x x' s in
        (* return the limited arrow type *)
        A.T_Arrow (x', s_sub, t')
    | _ -> failwith "todo"
  in
  limit' g m m ty

let rec meet (t1 : A.ty) (t2 : A.ty) : A.ty =
  match (t1, t2) with
  | A.T_Refined (b1, v1, p1), A.T_Refined (b2, v2, p2) ->
      if b1 = b2 then
        A.T_Refined (b1, v1, L.P_Conj (p1, L.substitute_pred v2 v1 p2))
      else raise (Switch_error "Constructor mismatch")
  | A.T_Arrow (x1, s1, t1), A.T_Arrow (x2, s2, t2) ->
      A.T_Arrow (x1, meet s1 s2, meet t1 (substitute_type x2 x1 t2))
  | _ -> raise (Switch_error "Constructor mismatch")

let unapply (g : env) (y : A.var) (zs : A.var list) (ty : A.ty) :
    env * (A.var * A.ty) list =
  let rec unapply' acc g zs t =
    match (zs, t) with
    | z :: zs', A.T_Arrow (x, s, t) ->
        unapply' ((z, s) :: acc) ((z, s) >: g) zs' (substitute_type x z t)
    | [], ty ->
        let t =
          match lookup g y with
          | Some t -> t
          | None ->
              raise (Switch_error "Variable being matched not in environment")
        in
        (g, (y, meet t ty) :: acc)
    | _ -> raise (Switch_error "Constructor mismatch")
  in
  unapply' [] g zs ty

let switch_alternatives_exhaustive (dctors : (A.var * A.ty) list)
    (alts : A.alt list) =
  let rec number_of_args (t : A.ty) =
    match t with
    | A.T_Refined _ -> 0
    | A.T_Arrow (_, _, t') -> 1 + number_of_args t'
  in
  let matches (A.Alt (dcname, binders, _) : A.alt) (dcname', t) =
    dcname = dcname' && List.length binders = number_of_args t
  in
  let alt_matched_in_dctors (alt : A.alt) =
    List.exists (fun dctor -> matches alt dctor) dctors
  in
  let dctor_matched_in_alts (dctor : A.var * A.ty) =
    List.exists (fun alt -> matches alt dctor) alts
  in
  List.for_all alt_matched_in_dctors alts
  && List.for_all dctor_matched_in_alts dctors

let check ?(fs = []) ?(debug = false) ?(denv = []) (g : env) (e : A.expr)
    (ty : A.ty) : L.constraint_ =
  let rec check_alt (g : env) (y : A.var) (A.Alt (dcname, zs, e) : A.alt)
      (ty : A.ty) : L.constraint_ =
    let s =
      match lookup_dctor_ty denv dcname with
      | Some s -> s
      | None -> raise (Switch_error "Constructor not in environment")
    in
    let g', zs_ts = unapply g y zs s in
    let c = check' g' e ty in
    List.fold_left (fun c (x, t) -> implication x t c) c zs_ts
  and check'' (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
    (* returned constraints are not necessarily closed *)
    match e with
    | E_Let (x, e1, e2) ->
        (* Check that we try to bind under an identifier that clashes with a type or data constructor *)
        if lookup_tctor denv x <> None || lookup_dctor_ty denv x <> None then
          raise
            (Bind_error
               "Attempted to bind a variable under the same identifier as a \
                data constructor (let)")
        else
          let c1, t1 = synth g e1 in

          let c2 = check' ((x, t1) >: g) e2 ty in
          L.C_Conj (c1, implication x t1 c2)
    | E_RLet (f, e1, t1, m, e2) ->
        (* Check that we try to bind under an identifier that clashes with a type or data constructor *)
        if lookup_tctor denv f <> None || lookup_dctor_ty denv f <> None then
          raise
            (Bind_error
               "Attempted to bind a variable under the same identifier as a \
                data constructor (let-rec)")
        else
          let t1', m' = rename_ty e1 t1 m in
          let ys, e1_body, t1_result = split_lambdas (e1, t1') in
          let tlim = limit_function fs g m' t1' in
          let g' = List.fold_right ( >: ) ys g in
          (* check body of e1 with limited f *)
          let c1 = check' ((f, tlim) >: g') e1_body t1_result in
          (* check remaining e2 with non-limited f *)
          let c2 = check' ((f, t1') >: g') e2 ty in
          L.C_Conj (implications ys c1, c2)
    | E_Abs (x, e) -> (
        match ty with
        | A.T_Arrow (_, s, t) ->
            let c = check' ((x, s) >: g) e t in
            implication x s c
        | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
    | E_If (x, e1, e2) ->
        let y = fresh_var () in
        let c0 = check' g (A.E_Var x) (T_Refined (B_Bool, "b", L.P_True)) in
        let yt1 = A.T_Refined (B_Int, y, L.P_Var x) in
        let c1 = check' ((y, yt1) >: g) e1 ty in
        let yt2 = A.T_Refined (B_Int, y, L.P_Neg (L.P_Var x)) in
        let c2 = check' ((y, yt2) >: g) e2 ty in
        L.C_Conj (c0, L.C_Conj (implication y yt1 c1, implication y yt2 c2))
    | E_Switch (y, alts) -> (
        match lookup g y with
        | Some (A.T_Refined (A.B_TyCtor tc, _, _)) -> (
            match lookup_tctor denv tc with
            | Some (_, ctors) ->
                if switch_alternatives_exhaustive ctors alts then
                  List.fold_left
                    (fun c_acc a -> L.C_Conj (c_acc, check_alt g y a ty))
                    (L.C_Pred L.P_True) alts
                else raise (Switch_error "Switch non-exhaustive")
            | None ->
                raise (Switch_error "Constructors not in data environment"))
        | _ -> raise (Switch_error "Switch on non-value"))
    | e ->
        let c, s = synth g e in
        let c' = sub g s ty in
        L.C_Conj (c, c')
  and synth' (g : env) (e : A.expr) : L.constraint_ * A.ty =
    match e with
    | E_Const c ->
        let t =
          A.T_Refined (A.B_Int, "v", L.P_Op (L.O_Eq, L.P_Var "v", L.P_Int c))
        in
        (L.C_Pred L.P_True, t)
    | E_True ->
        let t = A.T_Refined (A.B_Bool, "v", L.P_Var "v") in
        (L.C_Pred L.P_True, t)
    | E_False ->
        let t = A.T_Refined (A.B_Bool, "v", P_Neg (L.P_Var "v")) in
        (L.C_Pred L.P_True, t)
    | E_Var v -> (
        (* To be able to rely on function application for constructing
           user-defined data types, first identify whether v is the name
           of a data constructor, and if that fails, look it up in the
           environment *)
        match (lookup_dctor_ty denv v, lookup g v) with
        | Some t, _ -> (L.C_Pred L.P_True, self v t)
        | None, Some t -> (L.C_Pred L.P_True, self v t)
        | _ ->
            raise
              (Synthesis_error
                 ("Could not lookup var '" ^ pp_expr e ^ "' in type env")))
    | E_App (e, y) -> (
        match synth g e with
        | c, T_Arrow (x, s, t) ->
            let c' = check' g (A.E_Var y) s in
            (L.C_Conj (c, c'), substitute_type x y t)
        | _, T_Refined _ ->
            raise (Synthesis_error "Expected exp to synthesize to arrow type"))
    | E_Ann (e, t) -> (check' g e t, t)
    | _ ->
        raise
          (Synthesis_error ("Could not synthesize expression: " ^ pp_expr e))
  and check' (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
    let _ =
      if debug then (
        print_indent !debug_indent;
        print "Γ: ";
        print @@ doc_to_string @@ pp_env @@ env_to_list g;
        print "\n";
        print_indent !debug_indent;
        print @@ pp_expr e;
        print " <== ";
        print @@ pp_type ty;
        print "\n";
        debug_indent := !debug_indent + 1)
    in
    let c = strip_trues @@ check'' g e ty in
    let _ =
      if debug then (
        debug_indent := !debug_indent - 1;
        print_indent !debug_indent;
        print "RES: ";
        print @@ doc_to_string @@ pp_constraint ~indent:!debug_indent c;
        print "\n")
    in
    c
  and synth (g : env) (e : A.expr) : L.constraint_ * A.ty =
    let _ =
      if debug then (
        print_indent !debug_indent;
        print "Γ: ";
        print @@ doc_to_string @@ pp_env @@ env_to_list g;
        print "\n";
        print_indent !debug_indent;
        print @@ pp_expr e;
        print " ==>\n";
        debug_indent := !debug_indent + 1)
    in
    let c, t = synth' g e in
    let c = strip_trues c in
    let _ =
      if debug then (
        debug_indent := !debug_indent - 1;
        print_indent !debug_indent;
        print "RES: (";
        print @@ doc_to_string @@ pp_constraint ~indent:!debug_indent c;
        print " , ";
        print @@ pp_type t;
        print "\n")
    in
    (c, t)
  in
  if debug then (
    print "𝛿: ";
    print @@ doc_to_string @@ pp_env @@ denv_to_list denv;
    print "\n\n";
  );
  fresh_var_count := 0;

  (* Check that the provided data environment is wellformed *)
  match check_data_env denv with
  | R.Ok denv ->
      (* returned constraints are closed *)
      close_data denv @@ close g @@ L.simplify_constr @@ check' g e ty
  | R.Error e -> raise e
