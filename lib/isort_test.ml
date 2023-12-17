open Demodata
open Parse

(* Lists of natural numbers: *)
(* ========================= *)

let nlist = string_to_ty_ctor
    {|
        type nlist =
         | Nil => {v: nlen(v) = 0}
         | Cons (x:int{n:n>=0}, xs:nlist)
               => {v: nlen(v) = 1 + nlen(xs)}.
     |}

let denv = Typecheck.build_data_env [ nlist ]

let%test "typechecking nlists" =
  let e =
    string_to_expr
      {|
         let x = 1 in Cons x Nil
      |}
  in
  let t = string_to_type "nlist" in
  let g = Typecheck.E_Empty in
  let fs = [ nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  Solver.check ~fs c

(* Ordered lists of natural numbers (descending): *)
(* ============================================== *)

let olist = string_to_ty_ctor
    {|
        type olist =
         | ONil => {v: max(v)=0 & len(v)=0}
         | OCons (x:int{x: x>=0},
                  xs:olist{xs: x >= max(xs)})
               => {v: max(v) = x & len(v)=len(xs)+1}.
     |}

let denv = Typecheck.build_data_env [ olist; nlist ]

let%test "typechecking olists" =
  let e =
    string_to_expr
      {|
       let x = 0 in
       let y = 2 in
       let z = 3 in
       let a = OCons x ONil in
       let b = OCons y a in OCons z b
     |}
  in
  let t = string_to_type "olist" in
  let g = Typecheck.base_env in
  let fs = [ max_; olen; nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  Solver.check ~fs c

(* Insertion sort: *)
(* =============== *)


let%test "insertion sort" =
  let e = string_to_expr
     {|
      let rec insert = (fn x. (fn xs.
        switch xs {
        | ONil => OCons x ONil
        | OCons(y, ys) =>
            let b = ge x y in
            if b
              then OCons x xs
              else let tl = insert x ys in
                OCons y tl
        })): x:int{v:v>=0} -> xs:olist
              -> olist{ys: len(ys)=len(xs)+1 &
                          ((~x>=max(xs) | max(ys)=x) &
                          (  x>=max(xs) | max(ys)=max(xs)))}
                 / len(xs)
      in
      let rec isort = (fn xs.
        switch xs {
        | Nil => ONil
        | Cons(y, ys) =>
            let tl = isort ys in insert y tl
        }): xs:nlist -> olist / nlen(xs)
      in
        44

      |}
  in
  let t = string_to_type "int" in
  let g = Typecheck.base_env in
  let fs = [ max_; olen; nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  Solver.check ~dbg:false ~fs c
