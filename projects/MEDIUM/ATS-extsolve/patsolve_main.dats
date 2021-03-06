(*
** ATS-extsolve:
** For solving ATS-constraints
** with external SMT-solvers
*)

(*
** Author: Hongwei Xi
** Authoremail: gmhwxiATgmailDOTcom
*)

#include "share/atspre_staload.hats"

staload "./patsolve_commarg.sats"

(* dynload "patsolve_cnstrnt.dats" *)

val () = patsolve_cnstrnt__dynload() where
  {
    extern fun patsolve_cnstrnt__dynload(): void = "ext#"
  }
  
(* dynload "patsolve_parsing.dats" *)

val () = patsolve_parsing__dynload() where
  {
    extern fun patsolve_parsing__dynload(): void = "ext#"
  }

(* dynload "patsolve_commarg.dats" *)
val () = patsolve_commarg__dynload() where
  {
    extern fun patsolve_commarg__dynload(): void = "ext#"
  }

implement main0 (argc, argv) =
  {
    val () = println! ("Hello from [patsolve]!")
    
    val arglst = patsolve_cmdline (argc, argv)
    
    // skip first arg
    val- ~list_vt_cons(_, arglst) = arglst
    
    val () = patsolve_commarglst (arglst)
  }
