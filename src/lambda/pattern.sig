(* Pattern Substitutions *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature PATTERN = 
sig
  structure IntSyn : INTSYN

  val checkSub : IntSyn.Sub -> bool
  val dotEta   : IntSyn.Front * IntSyn.Sub -> IntSyn.Sub

  exception Eta
  val etaContract : IntSyn.Exp -> int	(* can raise Eta *)
end;  (* signature PATTERN *)
