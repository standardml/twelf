(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CONV =
sig
  structure IntSyn : INTSYN
	
  val conv : IntSyn.eclo * IntSyn.eclo -> bool
end;  (* signature CONV *)
