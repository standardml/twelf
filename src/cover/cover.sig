(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig

  (*! structure IntSyn : INTSYN !*)
  structure ModeSyn : MODESYN
  (*! sharing ModeSyn.IntSyn = IntSyn !*)

  exception Error of string

  val checkNoDef : IntSyn.cid -> unit	(* raises Error(msg) *)

  val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

end;  (* signature COVER *)
