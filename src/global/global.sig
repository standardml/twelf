(* Global parameters *)
(* Author: Frank Pfenning *)

signature GLOBAL =
sig
  val chatter : int ref
  val style : int ref
  val maxCid : int
  val maxMid : int
  val maxCSid : int
  val doubleCheck : bool ref
  val unsafe : bool ref
  val chPrint : int -> (unit -> string) -> unit
end;  (* signature GLOBAL *)
