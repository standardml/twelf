(* Coverage Checking *)
(* Author: Frank Pfenning *)

signature COVER =
sig

  structure IntSyn : INTSYN
  structure ModeSyn : MODESYN
    sharing ModeSyn.IntSyn = IntSyn

  exception Error of string

  val checkCovers : (IntSyn.cid * ModeSyn.ModeSpine) -> unit

end;  (* signature COVER *)
