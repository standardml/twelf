(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CONV =
sig
  (*! structure IntSyn : INTSYN !*)

  val conv : IntSyn.eclo * IntSyn.eclo -> bool
  val convDec : (IntSyn.Dec * IntSyn.Sub) * (IntSyn.Dec * IntSyn.Sub)-> bool
  val convSub : IntSyn.Sub * IntSyn.Sub -> bool
end;  (* signature CONV *)
