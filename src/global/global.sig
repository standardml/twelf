(* Global parameters *)
(* Author: Frank Pfenning *)

signature GLOBAL =
sig
  val chatter : int ref
  val maxCid : int
  val doubleCheck : bool ref
  val safe : bool ref
end;  (* signature GLOBAL *)
