(*
** libatscc2py_pygame
*)

(* ****** ****** *)
//
// HX-2016-05:
// prefix for external names
//
(* ****** ****** *)

#define
ATS_EXTERN_PREFIX "ats2py_pygame_"

(* ****** ****** *)
//
staload "./../../basics_py.sats"
//
(* ****** ****** *)

abstype Rect

(* ****** ****** *)
//
abstype Event
//
typedef Eventlist = PYlist(Event)
//
abstype Event_type
//
(* ****** ****** *)

fun
Rect_make
(
  t: int, l: int, b: int, r: int
) : Rect = "mac#%" 

(* ****** ****** *)
//
fun
Rect_copy(Rect): Rect = "mac#%"
//
overload .copy with Rect_copy
//
(* ****** ****** *)
//
fun
Rect_fit(Rect, Rect): Rect = "mac#%"
//
overload .fit with Rect_fit
//
fun
Rect_clip(Rect, Rect): Rect = "mac#%"
//
overload .clip with Rect_clip
//
(* ****** ****** *)
//
fun
Rect_contains(Rect, Rect): bool = "mac#%"
//
overload .contains with Rect_contains
//
(* ****** ****** *)
//
fun
Rect_move
  (Rect, x: int, y: int): Rect = "mac#%"
fun
Rect_move_ip
  (Rect, x: int, y: int): void = "mac#%"
//
overload .move with Rect_move
overload .move_ip with Rect_move_ip
//
(* ****** ****** *)
//
fun
Rect_inflate
  (Rect, x: int, y: int): Rect = "mac#%"
fun
Rect_inflate_ip
  (Rect, x: int, y: int): void = "mac#%"
//
overload .inflate with Rect_inflate
overload .inflate_ip with Rect_inflate_ip
//
(* ****** ****** *)
//
fun
Rect_clamp(Rect, Rect): Rect = "mac#%"
fun
Rect_clamp_ip(Rect, Rect): void = "mac#%"
//
overload .clamp with Rect_clamp
overload .clamp_ip with Rect_clamp_ip
//
(* ****** ****** *)
//
fun
Rect_union(Rect, Rect): Rect = "mac#%"
fun
Rect_union_ip(Rect, Rect): void = "mac#%"
//
overload .union with Rect_union
overload .union_ip with Rect_union_ip
//
(* ****** ****** *)

(*
QUIT             none
ACTIVEEVENT      gain, state
KEYDOWN          unicode, key, mod
KEYUP            key, mod
MOUSEMOTION      pos, rel, buttons
MOUSEBUTTONUP    pos, button
MOUSEBUTTONDOWN  pos, button
JOYAXISMOTION    joy, axis, value
JOYBALLMOTION    joy, ball, rel
JOYHATMOTION     joy, hat, value
JOYBUTTONUP      joy, button
JOYBUTTONDOWN    joy, button
VIDEORESIZE      size, w, h
VIDEOEXPOSE      none
USEREVENT        code
*)
//
macdef
QUIT = $extval(Event_type, "QUIT")
//
macdef
KEYUP = $extval(Event_type, "KEYUP")
macdef
KEYDOWN = $extval(Event_type, "KEYDOWN")
//
macdef
USEREVENT = $extval(Event_type, "USEREVENT")
//
macdef
ACTIVEEVENT = $extval(Event_type, "ACTIVEEVENT")
//
macdef
MOUSEMOTION = $extval(Event_type, "MOUSEMOTION")
//
macdef
MOUSEBUTTONUP = $extval(Event_type, "MOUSEBUTTONUP")
macdef
MOUSEBUTTONDOWN = $extval(Event_type, "MOUSEBUTTONDOWN")
//
macdef
VIDEORESIZE = $extval(Event_type, "VIDEORESIZE")
macdef
VIDEOEXPOSE = $extval(Event_type, "VIDEOEXPOSE")
//
macdef
JOYBUTTONUP = $extval(Event_type, "JOYBUTTONUP")
macdef
JOYBUTTONDOWN = $extval(Event_type, "JOYBUTTONDOWN")
//
macdef
JOYHATMOTION = $extval(Event_type, "JOYHATMOTION")
macdef
JOYAXISMOTION = $extval(Event_type, "JOYAXISMOTION")
macdef
JOYBALLMOTION = $extval(Event_type, "JOYBALLMOTION")
//
(* ****** ****** *)
//
fun event_pump(): void = "mac#%"
//
(* ****** ****** *)
//
fun event_get(): Eventlist = "mac#%"
fun event_get_type(Event_type): Eventlist = "mac#%"
//
(* ****** ****** *)
//
fun event_poll(): Event = "mac#%"
//
(* ****** ****** *)
//
fun event_wait(): Event = "mac#%"
//
(* ****** ****** *)
//
fun event_clear(): void = "mac#%"
fun event_clear_type(Event_type): void = "mac#%"
//
(* ****** ****** *)
//
fun event_post(Event): void = "mac#%"
//
(* ****** ****** *)
//
fun
event_event_name(Event_type): string = "mac#%"
//
(* ****** ****** *)
//
fun
event_set_blocked(): bool = "mac#%"
fun
event_set_blocked_type(Event_type): bool = "mac#%"
//
(* ****** ****** *)
//
fun
event_set_allowed(): bool = "mac#%"
fun
event_set_allowed_type(Event_type): bool = "mac#%"
//
(* ****** ****** *)
//
fun
event_get_blocked(Event_type): bool = "mac#%"
//
(* ****** ****** *)

(* end of [pygame.sats] *)
