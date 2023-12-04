open Pp
module A = Ast
module L = Logic
module R = Result

let r_bind f r x = R.bind r (f x)

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

(* notation *)
let ( >: ) (v, t) g = E_Cons (v, t, g)
let ( ==> ) x p = L.( ==> ) x p

let base_env =
  ("add", Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x+y)}")
  >: (( "sub",
        Parse.string_to_type "x:int{v:True}->y:int{v:True}->int{z:z=(x-y)}" )
     >: E_Empty)

exception Invalid_arrow_type of string
exception Synthesis_error of string
exception Subtyping_error of string
exception Switch_error of string
exception Data_env_illformed_error of string
exception Bind_error of string

let debug = ref false

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
  | A.T_Refined (bt, v, p) -> (x, ty_to_sort bt, L.substitute_pred p v x) ==> c
  | _ -> c

(* Computes t[y := z] in a capture avoiding manner, see RTT 3.1 *)
let rec substitute_type (t : A.ty) (y : A.var) (z : A.var) : A.ty =
  match t with
  | T_Refined (b, v, p) ->
      if String.equal v y then t else T_Refined (b, v, L.substitute_pred p y z)
  | T_Arrow (v, s, t) ->
      if String.equal v y then T_Arrow (v, substitute_type s y z, t)
      else T_Arrow (v, substitute_type s y z, substitute_type t y z)

let rec sub (s : A.ty) (t : A.ty) : L.constraint_ =
  match s with
  | T_Refined (b, v1, p1) -> (
      match t with
      | T_Refined (b', v2, p2) ->
          if not (b = b') then
            raise (Subtyping_error "Refined types have different base types")
          else (v1, ty_to_sort b, p1) ==> L.C_Pred (L.substitute_pred p2 v2 v1)
      | T_Arrow _ -> raise (Subtyping_error "Expected refined type"))
  | T_Arrow (x1, s1, t1) -> (
      match t with
      | T_Arrow (x2, s2, t2) ->
          let ci = sub s2 s1 in
          let co = sub (substitute_type t1 x1 x2) t2 in
          L.C_Conj (ci, implication x2 s2 co)
      | T_Refined _ -> raise (Subtyping_error "Expected arrow type"))

(* selfification, see Section 4 *)
let self (v : A.var) (t : A.ty) : A.ty =
  match t with
  | T_Refined (b, v', p) ->
      T_Refined (b, v', L.P_Conj (p, L.P_Op (O_Eq, P_Var v, P_Var v')))
  | T_Arrow _ -> t

let fresh_var (g : env) : A.var =
  let rec fresh_var' (suffix_candidate : int) =
    let var_cand = "fr" ^ Printf.sprintf "%d" suffix_candidate in
    match lookup g var_cand with
    | None -> var_cand
    | Some _ -> fresh_var' (suffix_candidate + 1)
  in
  fresh_var' 0

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

let rec meet (t1 : A.ty) (t2 : A.ty) : A.ty =
  match (t1, t2) with
  | A.T_Refined (b1, v1, p1), A.T_Refined (b2, v2, p2) ->
      if b1 = b2 then
        A.T_Refined (b1, v1, L.P_Conj (p1, L.substitute_pred p2 v2 v1))
      else raise (Switch_error "Constructor mismatch")
  | A.T_Arrow (x1, s1, t1), A.T_Arrow (x2, s2, t2) ->
      A.T_Arrow (x1, meet s1 s2, meet t1 (substitute_type t2 x2 x1))
  | _ -> raise (Switch_error "Constructor mismatch")

let unapply (g : env) (y : A.var) (zs : A.var list) (ty : A.ty) :
    env * (A.var * A.ty) list =
  let rec unapply' acc g zs t =
    match (zs, t) with
    | z :: zs', A.T_Arrow (x, s, t) ->
        unapply' ((z, s) :: acc) ((z, s) >: g) zs' (substitute_type t x z)
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

let check ?(denv = []) (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
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
  and check' (g : env) (e : A.expr) (ty : A.ty) : L.constraint_ =
    (* returned constraints are not necessarily closed *)
    let _ =
      if !debug then (
        print "check'";
        dbg @@ pp_expr' e;
        dbg @@ pp_ty ty)
    in
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
    | E_RLet (x, e1, t1, e2) ->
        (* Check that we try to bind under an identifier that clashes with a type or data constructor *)
        if lookup_tctor denv x <> None || lookup_dctor_ty denv x <> None then
          raise
            (Bind_error
               "Attempted to bind a variable under the same identifier as a \
                data constructor (let-rec)")
        else
          let g1 = (x, t1) >: g in
          (* NOTE: Fig. 4.5 in RTT has a typo, e1 should be checked againts t1, see fig. 4.2 *)
          let c1 = check' g1 e1 t1 in
          let c2 = check' g1 e2 ty in
          L.C_Conj (c1, c2)
    | E_Abs (x, e) -> (
        match ty with
        | A.T_Arrow (_, s, t) ->
            let c = check' ((x, s) >: g) e t in
            implication x s c
        | _ -> raise (Invalid_arrow_type "Expected arrow type on E_Abs"))
    | E_If (x, e1, e2) ->
        let y = fresh_var g in
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
        let c' = sub s ty in
        L.C_Conj (c, c')
  and synth (g : env) (e : A.expr) : L.constraint_ * A.ty =
    let _ =
      if !debug then (
        print "synth";
        dbg @@ pp_expr' e)
    in
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
        (* To be able to rely on function application for constructing user-defined data types, first identify whether v is the name of a data constructor, and if that fails, look it up in the environment *)
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
            (L.C_Conj (c, c'), substitute_type t x y)
        | _, T_Refined _ ->
            raise (Synthesis_error "Expected exp to synthesize to arrow type"))
    | E_Ann (e, t) -> (check' g e t, t)
    | _ ->
        raise
          (Synthesis_error ("Could not synthesize expression: " ^ pp_expr e))
  in
  (* Check that the provided data environment is wellformed *)
  match check_data_env denv with
  | R.Ok denv ->
      (* returned constraints are closed *)
      close_data denv @@ close g (check' g e ty)
  | R.Error e -> raise e
