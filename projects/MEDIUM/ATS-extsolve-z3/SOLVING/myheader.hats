(*
##
## ATS-extsolve-z3:
## Solving ATS-constraints with Z3
##
*)

#define Z3_targetloc "$PATSHOMERELOC/contrib/SMT/Z3"
#define PATSOLVE_targetloc "./../.ATS-extsolve"

staload "{$Z3}/SATS/z3.sats"

staload "{$PATSOLVE}/patsolve_cnstrnt.sats"

staload "./../patsolve_z3_solving.sats"
