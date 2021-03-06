(* ****** ****** *)
//
// For testing libatscc2pl
//
(* ****** ****** *)
//
#include "./../staloadall.hats"
//
(* ****** ****** *)
//
#define
ATS_MAINATSFLAG 1
#define
ATS_DYNLOADNAME "test02_dynload"
#define
ATS_STATIC_PREFIX "test02__"
//
(* ****** ****** *)

#define :: list_cons

(* ****** ****** *)

val xs =
(
  0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: 8 :: 9 :: nil()
) : List0 (int)

(* ****** ****** *)

val () = println! ("xs = ", xs)
val () = println! ("xs + xs = ", xs + xs)

(* ****** ****** *)

%{^
//
require "./../libatscc2pl_all.pl";
//
%} // end of [%{^]

(* ****** ****** *)

%{$
test02_dynload();
%} // end of [%{$]

(* ****** ****** *)

(* end of [test02.dats] *)
