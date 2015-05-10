(*
** ATS-extsolve:
** For solving ATS-constraints
** with external SMT-solvers
*)

(* ****** ****** *)

(*
** Author: Hongwei Xi
** Authoremail: gmhwxiATgmailDOTcom
*)

(* ****** ****** *)
//
#include
"share/atspre_staload.hats"
//
(* ****** ****** *)
//
staload
"./patsolve_constraint3.sats"
//
(* ****** ****** *)

typedef
s2Var_struct = @{
  s2Var_stamp= stamp
} (* end of [s2Var_struct] *)

(* ****** ****** *)

local
//
assume
s2Var_type =
  ref (s2Var_struct)
//
in (* in-of-local *)

implement
s2Var_get_stamp (s2V) = !s2V.s2Var_stamp

end // end of [local]

(* ****** ****** *)

implement
fprint_s2Var
  (out, s2V) =
  fprint! (out, "s2Var(", s2V.stamp, ")")
// end of [fprint_s2Var]

(* ****** ****** *)

(* end of [patsolve_constraint3_s2vvar.dats] *)
