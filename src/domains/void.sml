(* Collapsed Field *)
(* Author: Roberto Virga *)

structure Void : DOMAIN =
struct

  val name = "void"

  type number = unit

  val zero = ()
  val one  = ()

  exception Div

  fun op~ (_) = ()

  fun op+ (_, _) = ()

  fun op- (_, _) = ()

  fun op* (_, _) = ()

  fun inverse (_) = raise Div

  fun fromInt (_) = ()

  fun fromString (str) =
    if str = "0" then SOME ()
    else NONE

  fun toString (_) = "0"

end; (* structure Void *)







