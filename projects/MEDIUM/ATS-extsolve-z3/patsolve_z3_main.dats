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

staload "./patsolve_z3_commarg.sats"
staload "./patsolve_z3_solving.sats"

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


dynload "./patsolve_z3_commarg.dats"
dynload "./patsolve_z3_solving.dats"


implement main0 (argc, argv) =
  {
    val () = println! ("Hello from [patsolve_z3]!")
    
    val () = the_s2cinterp_initize()
    
    val arglst = patsolve_z3_cmdline (argc, argv)
    
    // skipping argv[0]
    val- ~list_vt_cons(_, arglst) = arglst
    
    val () = patsolve_z3_commarglst(arglst)
  }
