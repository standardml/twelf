(* Timers collecting statistics about Twelf *)
(* Author: Frank Pfenning *)

signature TIMERS =
sig

  structure Timing : TIMING

  (* Programming interface *)
  val parsing     : Timing.center		(* lexing and parsing *)
  val recon       : Timing.center		(* term reconstruction *)
  val abstract    : Timing.center		(* abstraction after reconstruction *)
  val checking    : Timing.center		(* redundant type-checking *)
  val modes       : Timing.center		(* mode checking *)
  val subordinate : Timing.center	        (* construction subordination relation *)
  val printing    : Timing.center		(* printing *)
  val compiling   : Timing.center		(* compilation *)
  val solving     : Timing.center		(* solving queries *)
  val coverage    : Timing.center               (* coverage checking *)
  val worlds      : Timing.center	        (* world checking *)
  val ptrecon     : Timing.center		(* solving queries using ptskeleon *)
  val filling     : Timing.center		(* filling in m2 *)
  val filltabled  : Timing.center		(* filling in m2 *)
  val recursion   : Timing.center		(* recursion in m2 *)
  val splitting   : Timing.center		(* splitting in m2 *)
  val inference   : Timing.center		(* inference in m2 *)
  val terminate   : Timing.center		(* checking termination *)
  val delphin     : Timing.center               (* Operational Semantics of Delphin *)

  (* Warning: time for printing of the answer substitution to a
     query is counted twice here.
  *)
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

end;  (* signature TIMERS *)
