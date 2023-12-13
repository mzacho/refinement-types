open Logic

let nlist_sort = S_TyCtor "nlist"

let nlen : uninterp_fun =
  ( "len",
    [ nlist_sort ],
    S_Int,
    Some
      (("l", nlist_sort, P_Op (O_Le, P_Int 0, P_FunApp ("len", [ P_Var "l" ])))
      ==> C_Pred P_True) )

let olist_sort = S_TyCtor "olist"

let max_ : uninterp_fun =
  ( "max",
    [ olist_sort ],
    S_Int,
    Some
      (("l", olist_sort, P_Op (O_Le, P_Int 0, P_FunApp ("max", [ P_Var "l" ])))
      ==> C_Pred P_True) )

let alist_sort = S_TyCtor "alist"

let amax : uninterp_fun =
  ( "max",
    [ alist_sort ],
    S_Int,
    Some
      (("l", alist_sort, P_Op (O_Le, P_Int 0, P_FunApp ("max", [ P_Var "l" ])))
      ==> C_Pred P_True) )

let isNil : uninterp_fun = ("isNil", [ alist_sort ], S_Bool, None)
