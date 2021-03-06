(*
** ATS-extsolve:
** For solving ATS-constraints
** with external SMT-solvers
*)

(*
** Author: Hongwei Xi
** Authoremail: gmhwxiATgmailDOTcom
*)

extern fun parse_h3ypo_node (jsonval): h3ypo_node

implement parse_h3ypo (jsnv0) = 
  let
    (* val () = println!( "parse_h3ypo: jsnv0 = ", jsnv0) *)
    val-JSONobject(lxs) = jsnv0
    val () = assertloc(length(lxs) >= 2)
    
    val+list_cons(lx, lxs) = lxs
    val loc = parse_location (lx.1)
    
    val+list_cons(lx, lxs) = lxs
    val node = parse_h3ypo_node (lx.1)
  in
    h3ypo_make_node (loc, node)
  end

local 

  fun aux_H3YPOprop ( x0: jsonval) : h3ypo_node = 
    let
      val-JSONarray(xs) = x0
      val-list_cons (x, xs) = xs
    in
      H3YPOprop(parse_s2exp(x))
    end
  
  fun aux_H3YPObind (x0: jsonval) : h3ypo_node = 
    let
      val-JSONarray(xs) = x0
      val-list_cons (x_1, xs) = xs
      val-list_cons (x_2, xs) = xs
    in
      H3YPObind(parse_s2var(x_1), parse_s2exp(x_2))
    end
  
  fun aux_H3YPOeqeq(x0: jsonval) : h3ypo_node = 
    let
      val-JSONarray(xs) = x0
      val-list_cons (x_1, xs) = xs
      val-list_cons (x_2, xs) = xs
    in
      H3YPOeqeq(parse_s2exp(x_1), parse_s2exp(x_2))
    end 

in

implement parse_h3ypo_node (jsnv0) = 
  let
    val-JSONobject(lxs) = jsnv0
    val-list_cons (lx, lxs) = lxs
    val name = lx.0 and jsnv2 = lx.1
  in
    case+ name of
      | "H3YPOprop" => aux_H3YPOprop(jsnv2)
      | "H3YPObind" => aux_H3YPObind(jsnv2)
      | "H3YPOeqeq" => aux_H3YPOeqeq(jsnv2)
      (*unrecognized*)
      | _ => let val () = assertloc(false) in exit(1) end
  end

end
