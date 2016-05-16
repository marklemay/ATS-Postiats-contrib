(*
** ATS-extsolve:
** For solving ATS-constraints
** with external SMT-solvers
*)

(*
** Author: Hongwei Xi
** Authoremail: gmhwxiATgmailDOTcom
*)

implement c3nstr_make_node (loc, c3tk, node) = 
  '{
    c3nstr_loc= loc, 
    c3nstr_kind= c3tk, c3nstr_node= node
  } 

implement fprint_c3nstr (out, c3t) =
  (
    case c3t.c3nstr_node of // case+
      | C3NSTRprop(s2e) => fprint! (out, "C3NSTRprop(", s2e, ")")
      | C3NSTRitmlst(s3is) => fprint! (out, "C3NSTRitmlst(", s3is, ")")
      | C3NSTRsolverify(s2e_prop) => fprint! (out, "C3NSTRsolverify(", s2e_prop, ")")
  )

implement fprint_c3nstropt(out, opt) = fprint_option(out, opt)

// pretty-printing
implement fpprint_c3nstr (out, c3t0) = 
  let
    fun aux_indent (ind: int): void =
      (
        if ind > 0
        then
          (
            fprint(out, ' '); aux_indent(ind-1)
          ) 
      )
    
    fun auxln_indent (ind: int): void = 
      (
        fprint! (out, '\n');
        aux_indent(ind)
      )
      
    fun aux_c3nstr ( ind: int, c3t0: c3nstr ) : void = 
      let
        val () = aux_indent(ind)
      in
        case+ c3t0.c3nstr_node of
          | C3NSTRprop(s2e) => fprint! (out, "C3NSTRprop(", s2e, ")")
          | C3NSTRitmlst(s3is) =>
            {
              val () = fprint! (out, "C3NSTRitmlst(\n")
              val () = aux_s3itmlst(ind+2, s3is)
              val () =
                (
                  aux_indent (ind); fprint (out, ") (* C3NSTRitmlst *)")
                ) 
            }
          | C3NSTRsolverify(s2e_prop) =>
            {
              val () = fprint! (out, "C3NSTRsolverify(", s2e_prop, ")")
            }
      end
      
    and aux_s3itm (ind: int, s3i0: s3itm) : void = 
      let
        val () = aux_indent(ind)
      in
        case+ s3i0 of
        | S3ITMsvar(s2v) => fprint! (out, "S3ITMsvar(", s2v, ")")
        | S3ITMsVar(s2V) => fprint! (out, "S3ITMsVar(", s2V, ")")
        | S3ITMhypo(h3p) => fprint! (out, "S3ITMhypo(", h3p, ")")
        | S3ITMcnstr(c3t) =>
          {
            val () = fprint! (out, "S3ITMcnstr(\n")
            val () = aux_c3nstr(ind+2, c3t)
            val () =
              (
                auxln_indent(ind); fprint! (out, ") (* S3ITMcnstr *)")
              )
          }
        | S3ITMcnstr_ref (loc, opt) => fprint! (out, "S3ITMcnstr_ref(", opt, ")")
        | S3ITMdisj(s3iss) => fprint! (out, "S3ITMdisj(", s3iss, ")")
        | S3ITMsolassert(s2e) => fprint! (out, "S3ITMsolassert(", s2e, ")")
      end 
      
    and aux_s3itmlst (ind: int, s3is: s3itmlst) : void =
      (
        case+ s3is of
          | list_nil () => ()
          | list_cons (s3i, s3is) =>
            (
              aux_s3itm(ind, s3i); fprint! (out, '\n'); aux_s3itmlst(ind, s3is)
            )
      )
  in
    aux_c3nstr(0, c3t0) //start indent at 0
  end 
