(*
** Session Co-List
*)

(* ****** ****** *)

#define ATS_DYNLOADFLAG 0

(* ****** ****** *)
//
#define
ATS_EXTERN_PREFIX "libats2erl_session_"
#define
ATS_STATIC_PREFIX "_libats2erl_session_list_"
//
(* ****** ****** *)
//
#include "share/atspre_define.hats"
#include "{$LIBATSCC2ERL}/staloadall.hats"
//
(* ****** ****** *)
//
staload
UN =
"prelude/SATS/unsafe.sats"
//
(* ****** ****** *)
//
staload "./../SATS/basis.sats"
staload "./../SATS/co-sslist.sats"
//
(* ****** ****** *)
//
staload "./basis_chan2.dats" // un-session-typed
//
(* ****** ****** *)

implement
chanpos_sslist
  (chpos) = let
//
val
chpos2 =
$UN.castvwtp1{chanpos2}(chpos)
//
val tag = chanpos2_recv{int}(chpos2)
//
prval () = $UN.cast2void(chpos2)
//
in
//
if
(tag=0)
then let
  prval () = $UN.castview2void(chpos) in chanpos_sslist_nil()
end // end of [then]
else let
  prval () = $UN.castview2void(chpos) in chanpos_sslist_cons()
end // end of [else]
//
end // end of [chanpos_list]

(* ****** ****** *)

implement
channeg_sslist_nil
  (chneg) = () where
{
//
val
chneg2 =
$UN.castvwtp1{channeg2}(chneg)
//
val () =
  channeg2_recv{int}(chneg2, 0)
//
prval () = $UN.cast2void(chneg2)
//
prval () = $UN.castview2void(chneg)
//
} (* end of [channeg_list_nil] *)

(* ****** ****** *)

implement
channeg_sslist_cons
  (chneg) = () where
{
//
val
chneg2 =
$UN.castvwtp1{channeg2}(chneg)
//
val () =
  channeg2_recv{int}(chneg2, 1)
//
prval () = $UN.cast2void(chneg2)
//
prval () = $UN.castview2void(chneg)
//
} (* end of [channeg_list_cons] *)

(* ****** ****** *)

implement
channeg_sslist_nil_close
  (chn) = let
//
val () = channeg_sslist_nil(chn) in channeg_nil_close(chn)
//
end // end of [channeg_sslist_nil_close]

(* ****** ****** *)

(* end of [co-sslist.dats] *)