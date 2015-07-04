(*
** For writing ATS code
** that translates into Erlang
*)

(* ****** ****** *)
//
// HX-2014-07
//
(* ****** ****** *)
//
staload "./basics_erl.sats"
//
(* ****** ****** *)
//
staload "./SATS/integer.sats"
//
(* ****** ****** *)
//
staload "./SATS/bool.sats"
staload "./SATS/float.sats"
//
(* ****** ****** *)
//
staload "./SATS/list.sats"
staload _ = "./DATS/list.dats"
//
(* ****** ****** *)
//
staload "./SATS/option.sats"
staload _ = "./DATS/option.dats"
//
(* ****** ****** *)
//
staload "./SATS/stream.sats"
staload _ = "./DATS/stream.dats"
//
(* ****** ****** *)

(* end of [staloadall.hats] *)