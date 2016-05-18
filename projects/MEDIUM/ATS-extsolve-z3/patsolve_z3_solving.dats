(*
##
## ATS-extsolve-z3:
## Solving ATS-constraints with Z3
##
*)

#include "share/atspre_define.hats"
#include "share/atspre_staload.hats"

staload UN = "prelude/SATS/unsafe.sats"

#define Z3_targetloc "$PATSHOMERELOC/contrib/SMT/Z3"
#define PATSOLVE_targetloc "./.ATS-extsolve"

staload "{$Z3}/SATS/z3.sats"

staload "{$PATSOLVE}/patsolve_cnstrnt.sats"
staload "{$PATSOLVE}/patsolve_parsing.sats"


staload "./patsolve_z3_solving.sats"

implement fprint_val<s2cst> = fprint_s2cst
implement fprint_val<s2var> = fprint_s2var
implement fprint_val<s2Var> = fprint_s2Var
implement fprint_val<s2exp> = fprint_s2exp
implement fprint_val<s3itm> = fprint_s3itm

extern fun c3nstr_solve_main  ( env: !smtenv, c3t: c3nstr, unsolved : &uint >> _, nerr: &int >> _) : int (*status*)


extern fun c3nstr_solve_errmsg (c3t: c3nstr, unsolved: uint): int

implement c3nstr_solve_errmsg (c3t, unsolved) = 
  0 where
  {
    val () = 
      (
        if unsolved = 0u
        then 
          let
            val out = stderr_ref
            val loc = c3t.c3nstr_loc
            val c3tk = c3t.c3nstr_kind
          in
            case+ c3tk of
              | C3TKmain() => ( fprintln! (out, "UnsolvedConstraint(main)@", loc, ":", c3t) )
              | C3TKtermet_isnat() => (fprintln! (out, "UnsolvedConstraint(termet_isnat)@", loc, ":", c3t) )
              | C3TKtermet_isdec() => (fprintln! (out, "UnsolvedConstraint(termet_isdec)@", loc, ":", c3t) )
              
              | _ => ( fprintln! (out, "UnsolvedConstraint(unclassified)@", loc, ":", c3t) )
          end
      )
  } 

extern fun c3nstr_solve_prop (loc0: loc_t, env: !smtenv, s2p: s2exp, nerr: &int >> _) : int (*status*)

extern fun c3nstr_solve_itmlst (loc0: loc_t, env: !smtenv, s3is: s3itmlst, unsolved: &uint >> _, nerr: &int >> _) : int (*status*)

extern fun c3nstr_solve_itmlst_cnstr (loc0: loc_t, env: !smtenv, s3is: s3itmlst, c3t: c3nstr, unsolved: &uint >> _, nerr: &int >> _) : int (*status*)

extern fun c3nstr_solve_itmlst_disj (loc0: loc_t, env: !smtenv, s3is: s3itmlst, s3iss: s3itmlstlst, unsolved: &uint >> _, nerr: &int >> _) : int (*status*) 

extern fun c3nstr_solve_solverify (loc0: loc_t, env: !smtenv, s2e_prop: s2exp, nerr: &int >> _) : int (*status*)

implement c3nstr_solve_prop(loc0, env, s2p, nerr) = 
  let
    val s2p = formula_make_s2exp (env, s2p)
  in
    smtenv_formula_solve (env, s2p)
  end

implement c3nstr_solve_itmlst (loc0, env, s3is, unsolved, nerr) = 
  let
    (* val () = println! ("c3str_solve_itmlst: s3is = ", s3is) *)
  in
    case+ s3is of
      | list_nil() => ~1 (*solved*)
      | list_cons(s3i, s3is) =>
        (
          case+ s3i of
            | S3ITMsvar(s2v) => 
              let
                val () = smtenv_add_s2var(env, s2v)
              in
                c3nstr_solve_itmlst(loc0, env, s3is, unsolved, nerr)
              end
            | S3ITMhypo(h3p) => 
              let
                val () = smtenv_add_h3ypo(env, h3p)
              in
                c3nstr_solve_itmlst(loc0, env, s3is, unsolved, nerr)
              end
            | S3ITMsVar(s2V) => c3nstr_solve_itmlst(loc0, env, s3is, unsolved, nerr)
            | S3ITMcnstr(c3t) => c3nstr_solve_itmlst_cnstr(loc0, env, s3is, c3t, unsolved, nerr)
            | S3ITMcnstr_ref(loc_ref, opt) =>
              (
                case+ opt of
                  | None() => ~1 (*solved*)
                  | Some(c3t) => c3nstr_solve_itmlst_cnstr(loc_ref, env, s3is, c3t, unsolved, nerr)
              )
            | S3ITMdisj(s3iss_disj) =>
              (
                c3nstr_solve_itmlst_disj(loc0, env, s3is, s3iss_disj, unsolved, nerr)
              ) 
            | S3ITMsolassert(s2e_prop) => 
              let
                val () = smtenv_add_s2exp(env, s2e_prop)
              in
                c3nstr_solve_itmlst(loc0, env, s3is, unsolved, nerr)
              end
        )
  end


implement c3nstr_solve_itmlst_cnstr(loc0, env, s3is, c3t, unsolved, nerr) = 
  let
    val (pf|()) = smtenv_push (env)
    val ans1 = c3nstr_solve_main (env, c3t, unsolved, nerr)
    val () = smtenv_pop (pf | env)
    val ans2 = c3nstr_solve_itmlst (loc0, env, s3is, unsolved, nerr)
  in
    if ans1 >= 0 
    then 0 (*unsolved*) 
    else ans2
  end 
  
(*s3iss disj*)
implement c3nstr_solve_itmlst_disj(loc0, env, s3is0, s3iss, unsolved, nerr) = 
  let
    (* val () = (println! ("c3nstr_solve_itmlst_disj: s3iss = ...")) *)
  in
    case+ s3iss of
      | list_nil() => ~1 (*solved*)
      | list_cons(s3is, s3iss) => 
        let
          val (pf|()) = smtenv_push (env)
          val s3is1 = list_append (s3is, s3is0)
          val ans = c3nstr_solve_itmlst (loc0, env, s3is1, unsolved, nerr)
          val () = smtenv_pop (pf | env)
        in
          c3nstr_solve_itmlst_disj (loc0, env, s3is0, s3iss, unsolved, nerr)
        end
  end 

implement c3nstr_solve_solverify(loc0, env, s2e_prop, nerr) = 
  let
    val s2e_prop = formula_make_s2exp (env, s2e_prop)
  in
    smtenv_formula_solve (env, s2e_prop)
  end


implement c3nstr_solve_main(env, c3t, unsolved, nerr) = 
  let
    val loc0 = c3t.c3nstr_loc
    var status: int =
      (
        // ~1: solved; 0: unsolved
        (* shoud be defined to make code more readable? *)
        case+ c3t.c3nstr_node of
        | C3NSTRprop(s2p) => c3nstr_solve_prop(loc0, env, s2p, nerr)
        | C3NSTRitmlst(s3is) => c3nstr_solve_itmlst(loc0, env, s3is, unsolved, nerr)
        | C3NSTRsolverify(s2e_prop) => c3nstr_solve_solverify(loc0, env, s2e_prop, nerr)
      ) : int
      
    val () = 
      (
        if status >= 0
        then 
          {
            val iswarn = c3nstr_solve_errmsg (c3t, unsolved)
            val () = if iswarn > 0 then (status := ~1)
          }
      )
      
    val () = if status >= 0 then (unsolved := unsolved + 1u)
  in
    status (* ~1/0: solved/unsolved *)
  end 


implement c3nstr_z3_solve (c3t0) = 
  let
    val env = smtenv_create()
    var unsolved: uint = 0u and err: int = 0
    
    (*ans*)
    val _ = c3nstr_solve_main (env, c3t0, unsolved, err)
    
    val () = smtenv_destroy (env)
  in (* why not just use an if here? *)
    case+ 0 of
      | _ when unsolved = 0u => 
        let
          val () = ( prerrln! "typechecking is finished successfully!" )
        in
          // nothing
        end
        
        (* unsolved > 0 *)
      | _ =>
        {
          val () = prerr "typechecking has failed"
          val () = if unsolved <= 1u then prerr ": there is one unsolved constraint"
          val () = if unsolved >= 2u then prerr ": there are some unsolved constraints"
          val () = (  prerrln! ": please inspect the above reported error message(s) for information." )
        }
  end

#define PATSOLVE_Z3_SOLVING 1

local
  #include "./SOLVING/patsolve_z3_solving_ctx.dats"
in
  // nothing
end

local
  #include "./SOLVING/patsolve_z3_solving_sort.dats"
in
  // nothing
end

local
  #include "./SOLVING/patsolve_z3_solving_form.dats"
in
  // nothing
end

local
  #include "./SOLVING/patsolve_z3_solving_smtenv.dats"
in
  // nothing
end

local
  #include "./SOLVING/patsolve_z3_solving_interp.dats"
in
  // nothing
end
