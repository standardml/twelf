(* Mode Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature MODECHECK =
sig

  structure ModeSyn : MODESYN
  structure Paths : PATHS

  exception  Error of string

  val checkD : ModeSyn.IntSyn.ConDec * Paths.occConDec option -> unit  (* raises Error *)

end;  (* signature MODECHECK *)
