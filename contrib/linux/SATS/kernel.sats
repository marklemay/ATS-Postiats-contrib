(* ****** ****** *)
//
// For applying ATS to
// linux-kernel programming
//
(* ****** ****** *)

%{#
//
#include \
"linux/CATS/kernel.cats"
//
%} // end of [%{#]

(* ****** ****** *)
//
staload PRINTK = "./printk.sats"
//
(* ****** ****** *)

(* end of [kernel.sats] *)
