(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig

  structure IntSyn : INTSYN
  structure ModeSyn : MODESYN
    sharing ModeSyn.IntSyn = IntSyn

  exception Error of string

  val checkOut : (IntSyn.dctx * IntSyn.Exp) -> unit

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

end;  (* signature COVER *)
