(*
** libatscc-common
*)

(* ****** ****** *)

staload "./../basics.sats"

(* ****** ****** *)
//
// HX-2013-04:
// intrange (l, r) is for integers i satisfying l <= i < r
//
(* ****** ****** *)
//
fun
int_repeat_lazy
  (n: int, f: lazy(void)): void = "mac#%"
fun
int_repeat_cloref
  (n: int, f: cfun0 (void)): void = "mac#%"
//
overload repeat with int_repeat_lazy of 100
overload repeat with int_repeat_cloref of 100
//
(* ****** ****** *)
//
fun
int_exists_cloref
  (n: int, f: cfun1 (int, bool)): bool = "mac#%"
fun
int_forall_cloref
  (n: int, f: cfun1 (int, bool)): bool = "mac#%"
//
fun
int_foreach_cloref
  (n: int, f: cfun1 (int, void)): void = "mac#%"
//
(* ****** ****** *)
//
fun
int_exists_method
  (n: int) (f: cfun1 (int, bool)): bool = "mac#%"
fun
int_forall_method
  (n: int) (f: cfun1 (int, bool)): bool = "mac#%"
fun
int_foreach_method
  (n: int) (f: cfun1 (int, void)): void = "mac#%"
//
overload .exists with int_exists_method of 100
overload .forall with int_forall_method of 100
overload .foreach with int_foreach_method of 100
//
(* ****** ****** *)
//
fun
int_foldleft_cloref
  {res:t@ype}
  (n: int, ini: res, f: cfun2 (res, int, res)): res = "mac#%"
//
fun
int_foldleft_method
  {res:t@ype}
  (int, TYPE(res))(ini: res, f: cfun2 (res, int, res)): res = "mac#%"
//
overload .foldleft with int_foldleft_method of 100
//
(* ****** ****** *)
//
fun
int_list_map_cloref
  {a:t0p}{n:nat}
  (n: int(n), fopr: cfun(int, a)): list(a, n)
fun
int_list_map_method
  {a:t0p}{n:nat}
  (n: int(n), TYPE(a))(fopr: cfun(int, a)): list(a, n)
//
overload .list_map with int_list_map_method
//
(* ****** ****** *)
//
fun
int2_exists_cloref
  (n1: int, n2: int, f: cfun2 (int, int, bool)): bool = "mac#%"
fun
int2_forall_cloref
  (n1: int, n2: int, f: cfun2 (int, int, bool)): bool = "mac#%"
//
fun
int2_foreach_cloref
  (n1: int, n2: int, f: cfun2 (int, int, void)): void = "mac#%"
//
(* ****** ****** *)
//
fun
intrange_exists_cloref
  (l: int, r: int, f: cfun1 (int, bool)): bool = "mac#%"
fun
intrange_forall_cloref
  (l: int, r: int, f: cfun1 (int, bool)): bool = "mac#%"
//
fun
intrange_foreach_cloref
  (l: int, r: int, f: cfun1 (int, void)): void = "mac#%"
//
(* ****** ****** *)
//
fun
intrange_foldleft_cloref
  {res:t@ype}
  (l: int, r: int, ini: res, fopr: cfun2(res, int, res)): res = "mac#%"
//
fun
intrange_foldleft_method
  {res:t@ype}
  ($tup(int, int), TYPE(res))(ini: res, f: cfun2(res, int, res)): res = "mac#%"
//
overload .foldleft with intrange_foldleft_method of 100
//
(* ****** ****** *)
//
fun
intrange2_exists_cloref
(
  l1: int, r1: int, l2: int, r2: int, f: cfun2 (int, int, bool)
) : bool = "mac#%" // end of [intrange2_exists_cloref]
fun
intrange2_forall_cloref
(
  l1: int, r1: int, l2: int, r2: int, f: cfun2 (int, int, bool)
) : bool = "mac#%" // end of [intrange2_forall_cloref]
//
fun
intrange2_foreach_cloref
(
  l1: int, r1: int, l2: int, r2: int, f: cfun2 (int, int, void)
) : void = "mac#%" // end of [intrange2_foreach_cloref]
//
(* ****** ****** *)

(* end of [intrange.sats] *)
