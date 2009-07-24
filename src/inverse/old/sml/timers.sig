
signature TIMERS =
sig

  (* Programming interface *)
  val checking    : Timing.center		(* redundant type-checking *)
  val eta_normal  : Timing.center		(* redundant type-checking *)
  val printing    : Timing.center		(* printing *)
  val translation : Timing.center		(* printing *)

  val total : Timing.sum		(* total time *)

  (* time center f x = y
     if f x = y and time of computing f x is added to center.
     If f x raises an exception, it is re-raised.
  *)
  val time : Timing.center -> ('a -> 'b) -> ('a -> 'b)

  (* External interface *)
  val reset : unit -> unit		(* reset above centers *)
  val check : unit -> unit		(* check timer values *)
  val show : unit -> unit		(* check, then reset *)

end
