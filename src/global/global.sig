(* Global parameters *)
(* Author: Frank Pfenning *)

signature GLOBAL =
sig
  val chatter : int ref
  val maxCid : int
  val maxCSid : int
  val doubleCheck : bool ref
  val unsafe : bool ref
end;  (* signature GLOBAL *)
