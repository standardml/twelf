(* Uniqueness Checking *)
(* Author: Frank Pfenning *)

signature UNIQUE =
sig

  structure ModeSyn : MODESYN

  exception Error of string

  val checkUnique : (IntSyn.cid * ModeSyn.ModeSpine) -> unit  (* raises Error(msg) *)

end;  (* signature UNIQUE *)
