open Demodata
open Parse

(* =============== DEMO ==================== *)

let%test "Simple let expression typechecks" =
  let e = string_to_expr {|
          let x = 12 in x
      |} in
  let t = string_to_type "int{v: v > 10}" in
  let g = Typecheck.E_Empty in
  (* Check that e has type t in g *)
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

(* Annotating fun abstractions *)

let%test "Simple fun application typechecks" =
  let e =
    string_to_expr
      {|
      let y = 42 in
      let id = (fn x. x): x:int -> int{v: v=x}
      in id y
      |}
  in
  let t = string_to_type "int{v: v = 42}" in
  let g = Typecheck.E_Empty in
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

(* Path sensitivity *)

let%test "path sensitivity: Abs typechecks" =
  let e =
    string_to_expr
      {|
      let zero = 0 in
      let abs =
        (fn x.
          let b = (lt x) zero in
            if b
            then (sub zero) x
            else x) : x:int -> int{v: v >= x}
      in
      let ten = 10 in abs ten
      |}
  in
  let t = string_to_type "int{v: v >= 10}" in
  let g = Typecheck.base_env in
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

let%test "path sensitivity: Disjunction typechecks" =
  let e =
    string_to_expr
      {|
      let disj =
        (fn a.
          (fn b.
            if a
            then true
            else b))
          : a:bool -> b:bool -> bool{v:v = (a | b)}
      in
      let f = true in
      disj f f
     |}
  in
  let g = Typecheck.E_Empty in
  let t = string_to_type "bool{b: b = True}" in
  let c = Typecheck.check ~debug:false g e t in
  Solver.check c

(* ========== User-defined datatypes ================= *)

(* basic enums *)

let de =
  let tc =
    string_to_ty_ctor
      {|
            type T =
              | A
              | B.
       |}
  in
  Typecheck.build_data_env [ tc ]

let%test "Basic enum" =
  let e = string_to_expr "let x = A in x" in
  let t = string_to_type "T" in
  let g = Typecheck.E_Empty in
  let c = Typecheck.check ~debug:false ~denv:de g e t in
  Solver.check c

let%test "Basic switch statements" =
  let e =
    string_to_expr
      {|
      let x = A in
        switch x {
        | A => true
        | B => false
        }
      |}
  in
  let t = string_to_type "bool{v:True}" in
  let g = Typecheck.E_Empty in
  let c = Typecheck.check ~debug:false ~denv:de g e t in
  Solver.check c

(* int lists *)

let de =
  let tc =
    string_to_ty_ctor
      {|
        type nlist =
         | Nil => {v: len(v) = 0}
         | Cons (x:int{n:n>=0}, xs:nlist)
               => {v: len(v) = 1 + len(xs)}.
       |}
  in
  Typecheck.build_data_env [ tc ]

let%test "sum natlist is positive" =
  let e =
    string_to_expr
      {|
     let rec sum =
       (fn l.
         switch l {
           | Nil => 0
           | Cons(x, xs) =>
               let y = sum xs in (add x) y
         }
       ) : l:nlist -> int{v:v >= 0} / len(l)
     in 42
     |}
  in
  let t = string_to_type "int{v:True}" in
  let g = Typecheck.base_env in
  let fs = [ nlen ] in
  let c = Typecheck.check ~fs ~debug:false ~denv:de g e t in
  Solver.check ~fs c

let%test "length of natlist" =
  let e =
    Parse.string_to_expr
      {|
        let one = 1 in
        let rec length =
          (fn l.
             switch l {
             | Cons(hd, tl) =>
                let x = length tl in add x one
             | Nil => 0
             }
          ) : l:nlist -> int{v: v = len(l)} / len(l)
       in
       let x = 0 in
       let y = (Cons x) Nil in
       let z = (Cons x) y in
       let l = (Cons x) z in length l
       |}
  in
  let t = string_to_type "int{v: v = 3}" in
  Solver.check ~fs:[ nlen ]
    (Typecheck.check ~fs:[ nlen ] ~denv:de Typecheck.base_env e t)

(* create a nlist from range of nats *)

let%test "range terminates: metrics can be decreasing expressions" =
  let e =
    Parse.string_to_expr
      {|
       let one = 1 in
       let rec range =
          (fn i.
            (fn j. let b = (lt i) j in
              if b
              then
                let newi = (add i) one in
                let tl = (range newi) j in (Cons i) tl
              else Nil))
          : i:int{i: i>=0} -> j:int -> nlist / j - i
       in
       let x = 12 in
       let y = 42 in (range x) y
     |}
  in
  let t = Parse.string_to_type "nlist" in
  let c = Typecheck.check ~fs:[ nlen ] ~denv:de Typecheck.base_env e t in
  Solver.check ~fs:[ nlen ] c

(* ordered lists by refining the tail with max *)

let denv =
  (* Lists of natural numbers: *)
  let nlist = string_to_ty_ctor
      {|
        type nlist =
         | Nil => {v: nlen(v) = 0}
         | Cons (x:int{n:n>=0}, xs:nlist)
               => {v: nlen(v) = 1 + nlen(xs)}.
       |} in
  (* Ordered lists of natural numbers (descending): *)
  let olist = string_to_ty_ctor
      {|
        type olist =
         | ONil => {v: max(v)=0 & len(v)=0}
         | OCons (x:int{x: x>=0}, xs:olist{xs: x >= max(xs)})
               => {v: max(v) = x & len(v)=len(xs)+1}.
       |} in
  Typecheck.build_data_env [ olist; nlist ]

let%test "[0] is an olist" =
  let e =
    string_to_expr
      {|
     let zero = 0 in
     let x = (OCons zero) ONil in x
     |}
  in
  let t = string_to_type "olist" in
  let g = Typecheck.base_env in
  let fs = [ max_; olen; nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  Solver.check ~fs c

let%test "[7;4;2] is an olist" =
  let e =
    string_to_expr
      {|
     let seven = 7 in let four = 4 in let two = 2 in
     let x = (OCons two) ONil in
     let y = (OCons four) x in
     let z = (OCons seven) y in z
     |}
  in
  let t = string_to_type "olist" in
  let g = Typecheck.base_env in
  let fs = [ max_; olen; nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  Solver.check ~fs c

let%test "[3; 4; 1] is not an olist" =
  let e =
    string_to_expr
      {|
     let three = 3 in let four = 4 in let one = 1 in
     let x = (OCons one) ONil in
     let y = (OCons four) x in
     let z = (OCons three) y in z
     |}
  in
  let t = string_to_type "olist" in
  let g = Typecheck.base_env in
  let fs = [ max_; olen; nlen' ] in
  let c = Typecheck.check ~fs ~debug:false ~denv g e t in
  not (Solver.check ~fs c)

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
                          ((~x>=max(xs)  | max(ys)=x) &
                          (  x>=max(xs)  | max(ys)=max(xs)))}
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

(* ==== termination checking  ==== *)

let%test "ackermann terminates: lexicographic metrics" =
  let e =
    Parse.string_to_expr
      {|
        let zero = 0 in let one = 1 in
        let rec ack =
        (fn m. (fn n.
          let b = (eq m) zero in
          if b then (add n) one
          else let newm = (sub m) one in
               let b = (eq n) zero in
               if b then (ack newm) one
               else let newn = (sub n) one in
                    let ackres = (ack m) newn in
                    (ack newm) ackres))
        : m:int{v:v>=0} -> n:int{v:v>=0} -> int{v:v>=0} / m, n
        in
        let x = 42 in
        let y = 1337 in (ack x) y
        |}
  in
  let t = Parse.string_to_type "int" in
  let c = Typecheck.check ~debug:false Typecheck.base_env e t in
  Solver.check ~dbg:false c

(* braid of two lists *)

let de =
  let tc =
    string_to_ty_ctor
      {|
        type nlist =
         | Nil => {v: len(v) = 0}
         | Cons (x:int , xs:nlist)
               => {v: len(v) = 1 + len(xs)}.
       |}
  in
  Typecheck.build_data_env [ tc ]

let%test "braid" =
  let e =
    Parse.string_to_expr
      {|
       let rec braid =
         (fn xs. (fn ys.
           switch xs {
           | Nil => ys
           | Cons(x, zs) =>
               let tl = braid ys zs in
               Cons x tl
           })) : xs:nlist -> ys:nlist -> nlist / len(xs) + len(ys)
       in
       let one = 43 in
       let xs = (Cons one) Nil in
       let ys = (Cons one) xs in (braid xs) ys
       |}
  in
  let t = Parse.string_to_type "nlist" in
  let c = Typecheck.check ~fs:[ nlen ] ~denv:de Typecheck.base_env e t in
  Solver.check ~fs:[ nlen ] c