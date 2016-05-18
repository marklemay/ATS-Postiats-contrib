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

staload STDIO = "libc/SATS/stdio.sats"

#define PATSOLVE_targetloc "./.ATS-extsolve"

staload "{$PATSOLVE}/patsolve_cnstrnt.sats"
staload "{$PATSOLVE}/patsolve_parsing.sats"

staload "./patsolve_z3_commarg.sats"
staload "./patsolve_z3_solving.sats"


implement fprint_commarg(out, ca) = 
  (
    case+ ca of
      | CAhelp(str) => fprint! (out, "CAhelp(", str, ")")
      | CAgitem(str) => fprint! (out, "CAgitem(", str, ")")
      | CAinput(str) => fprint! (out, "CAinput(", str, ")")
      | CAoutput(str) => fprint! (out, "CAoutput(", str, ")")
      | CAscript(str) => fprint! (out, "CAscript(", str, ")")
      | CAargend() => fprint! (out, "CAargend(", ")")
  ) 

fun{} argv_getopt_at {n:int}{i:nat} ( n: int n, argv: !argv(n), i: int i) : stropt =
  (
    if i < n then stropt_some (argv[i]) else stropt_none ()
  )

implement patsolve_z3_cmdline (argc, argv) = 
  let
    vtypedef res_vt = commarglst_vt
    
    fun aux {n:int} {i:nat | i <= n} ( argc: int n, argv: !argv(n), i: int i, res0: res_vt) : res_vt = 
      let (* TODO: this let seems unneedd *)
      in
        if i < argc
        then 
          let
            val arg = argv[i]
          in
            case+ arg of
              | "-h" => 
                let
                  val ca = CAhelp(arg)
                  val res0 = cons_vt(ca, res0)
                in
                  aux(argc, argv, i+1, res0)
                end
              | "--help" => 
                let
                  val ca = CAhelp(arg)
                  val res0 = cons_vt(ca, res0)
                in
                  aux(argc, argv, i+1, res0)
                end
              | "-i" => 
                let
                  val ca = CAinput(arg)
                  val res0 = cons_vt(ca, res0)
                in
                  aux(argc, argv, i+1, res0)
                end
              | "--input" => 
                let
                  val ca = CAinput(arg)
                  val res0 = cons_vt(ca, res0)
                in
                  aux(argc, argv, i+1, res0)
                end
                
              (*rest*)
              | _ => 
                let
                  val res0 = cons_vt(CAgitem(arg), res0)
                in
                  aux(argc, argv, i+1, res0)
                end
          end
          
        else res0 
      end
      
    val args = aux(argc, argv, 0, nil_vt)
    
  in
    list_vt_reverse(list_vt_cons(CAargend(), args))
  end


extern fun patsolve_z3_help(): void
extern fun patsolve_z3_input(): void
extern fun patsolve_z3_gitem(string): void
extern fun patsolve_z3_input_arg(string): void

extern fun patsolve_z3_argend(): void

extern fun patsolve_z3_commarglst_finalize(): void


typedef state_struct =
  @{
    nerr= int, input= int, ninput= int, fopen_inp= int, inpfil_ref= FILEref
  }

local
  var the_state: state_struct?
  
  val () = the_state.nerr := 0
  
  val () = the_state.input := 0
  val () = the_state.ninput := 0
  
  val () = the_state.fopen_inp := 0
  val () = the_state.inpfil_ref := stdin_ref
in
  val the_state : ref(state_struct) = ref_make_viewptr(view@the_state | addr@the_state)
end

fun process_arg (x: commarg): void = 
  let
    (* val () = fprintln!(stdout_ref, "patsolve_z3_commarglst: process_arg: x = ", x) *)
  in
    case+ x of
      | CAhelp _ => patsolve_z3_help ()
      | CAinput _ => patsolve_z3_input ()
      | CAgitem(str) => patsolve_z3_gitem(str)
      (*
      | CAoutput(str) => fprint! (out, "CAoutput(", str, ")")
      | CAscript(str) => fprint! (out, "CAscript(", str, ")")
      *)
      | CAargend() => patsolve_z3_argend ()
      (*rest-of-CA*) 
      | _ => ()
  end

implement patsolve_z3_commarglst (xs) = 
  let
    (* val () = println! ("patsolve_z3_commarglst") *)
  in
    case+ xs of
      | ~list_vt_cons (x, xs) => 
        let
          val () = process_arg(x)
        in
          patsolve_z3_commarglst (xs)
        end
      | ~list_vt_nil() => patsolve_z3_commarglst_finalize ()
  end

implement patsolve_z3_help() =
  {
    val () = prerrln! ("patsolve_z3_help: ...")
  }

implement patsolve_z3_input() =
  {
    (* val () = prerrln! ("patsolve_z3_input: ...") *)
    val () = !the_state.input := 1
  }

implement patsolve_z3_gitem(arg) = 
  let
    val () = prerrln! ("patsolve_z3_gitem: arg = ", arg)
    
    macdef input() = (!the_state.input > 0)
  in
    case+ 0 of
      | _ when input() =>
        {
          val () = patsolve_z3_input_arg(arg)
          val () = !the_state.ninput := !the_state.ninput+1
        }
        
        (*unrecognized*)
      | _  => ()
  end 


implement patsolve_z3_input_arg (path) = 
  let
    val opt = fileref_open_opt(path, file_mode_r)
  in
    case+ opt of
      | ~Some_vt(filr) =>
        {
          val n0 = !the_state.fopen_inp
          val () = !the_state.fopen_inp := 1
          
          val f0 = !the_state.inpfil_ref
          val () = if n0 > 0 then fileref_close(f0)
          val () = !the_state.inpfil_ref := filr
          
          val c3t0 = parse_fileref_constraints(filr)
      (*
          val () = fprint! ( stdout_ref, "patsolve_z3_input_arg: c3t0 =\n")
          val () = fpprint_c3nstr(stdout_ref, c3t0)
          val () = fprint_newline (stdout_ref)
      *)
          val () = c3nstr_z3_solve(c3t0)
          
        }
        
      | ~None_vt() =>
        {
          val n0 = !the_state.fopen_inp
          val () = !the_state.fopen_inp := 0
          
          val f0 = !the_state.inpfil_ref
          val () = if n0 > 0 then fileref_close(f0)
          val () = !the_state.inpfil_ref := stdin_ref
          
          val () =  prerrln! ("The file [", path, "] cannot be opened for read!")
        }
  end

implement patsolve_z3_argend() = 
  let=
    macdef test() = (!the_state.input > 0 && !the_state.ninput = 0)
  in
    case+ 0 of
      | _ when test() =>
        {
          val inp = stdin_ref
          val c3t0 =
          parse_fileref_constraints(inp)
          val () = c3nstr_z3_solve(c3t0)
        }
      | _ => ()
  end

implement patsolve_z3_commarglst_finalize() =
  {
    val n0 = !the_state.fopen_inp
    val f0 = !the_state.inpfil_ref
    val () = if n0 > 0 then fileref_close(f0)
  }
