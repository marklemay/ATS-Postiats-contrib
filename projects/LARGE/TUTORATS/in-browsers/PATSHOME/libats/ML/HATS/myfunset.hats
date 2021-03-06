(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(***********************************************************************)

(*
** ATS/Postiats - Unleashing the Potential of Types!
** Copyright (C) 2010-2015 Hongwei Xi, ATS Trustful Software, Inc.
** All rights reserved
**
** ATS is free software;  you can  redistribute it and/or modify it under
** the terms of  the GNU GENERAL PUBLIC LICENSE (GPL) as published by the
** Free Software Foundation; either version 3, or (at  your  option)  any
** later version.
**
** ATS is distributed in the hope that it will be useful, but WITHOUT ANY
** WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
** FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
** for more details.
**
** You  should  have  received  a  copy of the GNU General Public License
** along  with  ATS;  see the  file COPYING.  If not, please write to the
** Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
** 02110-1301, USA.
*)

(* ****** ****** *)

(* Author: Hongwei Xi *)
(* Authoremail: gmhwxiATgmailDOTcom *)
(* Start time: March, 2015 *)

(* ****** ****** *)
//
// HX-2015-03-14:
// For quickly building a funset interface
//
(* ****** ****** *)
//
(*
typedef elt = int/...
*)
//
(* ****** ****** *)
//
abstype
myset_type = ptr
//
typedef
myset = myset_type
//
(* ****** ****** *)

extern
fun
myfunset_nil():<> myset
and
myfunset_make_nil():<> myset

(* ****** ****** *)

extern
fun
myfunset_sing(elt): myset
and
myfunset_make_sing(elt): myset

(* ****** ****** *)

extern
fun
myfunset_make_list(List(elt)): myset

(* ****** ****** *)
//
extern
fun
fprint_myfunset
  (out: FILEref, xs: myset): void
//
overload fprint with fprint_myfunset
//
(* ****** ****** *)
//
extern
fun
myfunset_size(myset): size_t
//
overload .size with myfunset_size
//
(* ****** ****** *)
//
extern
fun
myfunset_is_member(myset, elt): bool
and
myfunset_isnot_member(myset, elt): bool
//
overload is_member with myfunset_is_member
overload isnot_member with myfunset_isnot_member
//
overload .is_member with myfunset_is_member
overload .isnot_member with myfunset_isnot_member
//
(* ****** ****** *)
//
extern
fun
myfunset_insert
  (xs: &myset >> _, x0: elt): bool
//
overload .insert with myfunset_insert
//
(* ****** ****** *)
//
extern
fun
myfunset_remove
  (xs: &myset >> _, x0: elt): bool
//
overload .remove with myfunset_remove
//
(* ****** ****** *)
//
extern
fun
myfunset_union(myset, myset): myset
and
myfunset_union2(&myset >> _, myset): void
//
overload union with myfunset_union
overload .union with myfunset_union2
//
extern
fun
myfunset_intersect(myset, myset): myset
and
myfunset_intersect2(&myset >> _, myset): void
//
overload intersect with myfunset_intersect
overload .intersect with myfunset_intersect2
//
(* ****** ****** *)
//
extern
fun
myfunset_differ
  (xs: myset, ys: myset): myset
and
myfunset_differ2
  (xs: &myset >> _, ys: myset): void
//
overload differ with myfunset_differ
overload .differ with myfunset_differ2
//
extern
fun
myfunset_symdiff
  (xs: myset, ys: myset): myset
and
myfunset_symdiff2
  (xs: &myset >> _, ys: myset): void
//
overload symdiff with myfunset_symdiff
overload .symdiff with myfunset_symdiff2
//
(* ****** ****** *)
//
extern
fun
myfunset_equal(myset, myset): bool
and
myfunset_notequal(myset, myset): bool
//
overload = with myfunset_equal
overload != with myfunset_notequal
//
(* ****** ****** *)
//
extern
fun
myfunset_compare(myset, myset): int
//
overload compare with myfunset_compare
//
(* ****** ****** *)
//
extern
fun
myfunset_is_subset(myset, myset): bool
and
myfunset_is_supset(myset, myset): bool
//
(* ****** ****** *)
//
overload is_subset with myfunset_is_subset
overload is_supset with myfunset_is_supset
//
overload .is_subset with myfunset_is_subset
overload .is_supset with myfunset_is_supset
//
(* ****** ****** *)
//
extern
fun
myfunset_foreach_cloref
  (myset, fwork: (elt) -<cloref1> void): void
//
extern
fun
myfunset_foreach_method
  (myset) (fwork: (elt) -<cloref1> void): void
//
overload .foreach with myfunset_foreach_method
//
(* ****** ****** *)
//
extern
fun
{res:t@ype}
myfunset_foldleft_cloref
(
  xs: myset
, ini: res, fopr: (res, elt) -<cloref1> res
) : res // end of [myfunset_foldleft_cloref]
//
extern
fun
{res:t@ype}
myfunset_foldleft_method
(
  myset, TYPE(res)
) (ini: res, fopr: (res, elt) -<cloref1> res): res
//
overload .foldleft with myfunset_foldleft_method
//
(* ****** ****** *)
//
extern
fun
myfunset_tabulate_cloref
  {n:nat}
(
  n: int(n), fopr: (natLt(n)) -<cloref1> elt
) : myset // end of [myfunset_tabulate_cloref]
//
extern
fun
myfunset_tabulate_method
  {n:nat}
  (n: int(n)) (fopr: (natLt(n)) -<cloref1> elt): myset
//
overload .tabulate with myfunset_tabulate_method
//
(* ****** ****** *)
//
extern
fun
myfunset_listize(myset): List0(elt)
//
overload listize with myfunset_listize
overload .listize with myfunset_listize
//
(* ****** ****** *)

local
//
staload
UN = "prelude/SATS/unsafe.sats"
//
staload "libats/ML/SATS/basis.sats"
staload "libats/ML/SATS/list0.sats"
staload "libats/ML/SATS/funset.sats"
//
staload _ = "libats/DATS/funset_avltree.dats"
//
staload _(*anon*) = "libats/ML/DATS/funset.dats"
//
assume myset_type = set_type(elt)
//
in (* in-of-local *)

(* ****** ****** *)
//
implement
myfunset_nil() = funset_make_nil{elt}()
implement
myfunset_make_nil() = funset_make_nil{elt}()
//
implement
myfunset_sing
  (x) = funset_make_sing<elt>(x)
implement
myfunset_make_sing
  (x) = funset_make_sing<elt>(x)
//
implement
myfunset_make_list
  (xs) = funset_make_list<elt>(g0ofg1(xs))
//
(* ****** ****** *)
//
implement
fprint_myfunset
  (out, xs) = fprint_funset<elt>(out, xs)
//
(* ****** ****** *)
//
implement
myfunset_size(xs) = funset_size<elt>(xs)
//
(* ****** ****** *)
//
implement
myfunset_is_member
  (xs, x0) = funset_is_member<elt>(xs, x0)
implement
myfunset_isnot_member
  (xs, x0) = funset_isnot_member<elt>(xs, x0)
//
(* ****** ****** *)
//
implement
myfunset_insert
  (xs, x0) = funset_insert<elt>(xs, x0)
//
implement
myfunset_remove
  (xs, x0) = funset_remove<elt>(xs, x0)
//
(* ****** ****** *)
//
implement
myfunset_union
  (xs, ys) = funset_union<elt>(xs, ys)
implement
myfunset_union2
  (xs, ys) = (xs := funset_union<elt>(xs, ys))
implement
myfunset_intersect
  (xs, ys) = funset_intersect<elt>(xs, ys)
implement
myfunset_intersect2
  (xs, ys) = (xs := funset_intersect<elt>(xs, ys))
//
(* ****** ****** *)
//
implement
myfunset_differ
  (xs, ys) = funset_differ<elt>(xs, ys)
implement
myfunset_differ2
  (xs, ys) = (xs := funset_differ<elt>(xs, ys))
implement
myfunset_symdiff
  (xs, ys) = funset_symdiff<elt>(xs, ys)
implement
myfunset_symdiff2
  (xs, ys) = (xs := funset_symdiff<elt>(xs, ys))
//
(* ****** ****** *)
//
implement
myfunset_equal
  (xs, ys) = funset_equal<elt>(xs, ys)
implement
myfunset_notequal
  (xs, ys) = ~(funset_equal<elt>(xs, ys))
//
implement
myfunset_compare
  (xs, ys) = funset_compare<elt>(xs, ys)
//
(* ****** ****** *)
//
implement
myfunset_is_subset
  (xs, ys) = funset_is_subset<elt>(xs, ys)
implement
myfunset_is_supset
  (xs, ys) = funset_is_supset<elt>(xs, ys)
//
(* ****** ****** *)
//
implement
myfunset_foreach_cloref
(
  xs, fwork
) = funset_foreach_cloref<elt>(xs, fwork)
//
implement
myfunset_foreach_method
  (xs) =
(
  lam (fwork) => myfunset_foreach_cloref(xs, fwork)
) (* myfunset_foreach_method *)
//
(* ****** ****** *)

implement
{res}(*tmp*)
myfunset_foldleft_cloref
  (xs0, ini, fopr) = r0 where
{
//
var r0
  : res = ini
//
val p_r0 = addr@r0
//
val ((*void*)) =
myfunset_foreach_cloref
(
  xs0
, lam(x) =>
  $UN.ptr0_set<res>
  (p_r0, fopr($UN.ptr0_get<res>(p_r0), x))
  // end of [lam]
) (* end of [myfunset_foreach_cloref] *)
//
} (* end of [myfunset_foldleft_cloref] *)
//
(* ****** ****** *)
//
implement
{res}(*tmp*)
myfunset_foldleft_method
  (xs0, tres) =
  lam (int, fopr) =>
  myfunset_foldleft_cloref<res> (xs0, int, fopr)
//
(* ****** ****** *)
//
implement
myfunset_tabulate_cloref
  (n, fopr) = funset_tabulate_cloref<elt>(n, fopr)
//
implement
myfunset_tabulate_method
  (n) = lam(fopr) => myfunset_tabulate_cloref(n, fopr)
//
(* ****** ****** *)
//
implement
myfunset_listize
  (xs) = g1ofg0_list(funset_listize<elt>(xs))
//
(* ****** ****** *)

end // end of [local]

(* ****** ****** *)

(* end of [myfunset.hats] *)
