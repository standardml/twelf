(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure ModeTable : MODESYN !*)
  (*! sharing ModeTable.IntSyn = IntSyn !*)

  exception Error of string

  val checkNoDef : IntSyn.cid -> unit	(* raises Error(msg) *)

  val checkOut : (IntSyn.dctx * IntSyn.eclo) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

end;  (* signature COVER *)
