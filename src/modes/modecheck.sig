(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature MODECHECK =
sig

  structure IntSyn : INTSYN
  structure ModeSyn : MODESYN
    sharing ModeSyn.IntSyn = IntSyn
  structure Paths : PATHS

  exception Error of string

  (* for new declarations *)
  val checkD : IntSyn.ConDec * string * Paths.occConDec option -> unit  (* raises Error (msg) *)

  (* for prior declarations *)
  val checkMode : IntSyn.cid * ModeSyn.ModeSpine -> unit (* raises Error(msg) *)

end;  (* signature MODECHECK *)
