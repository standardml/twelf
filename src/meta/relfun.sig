(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

signature RELFUN = 
sig
  structure FunSyn : FUNSYN

  exception Error of string

  val convertFor : FunSyn.IntSyn.cid list -> FunSyn.For
  val convertPro : FunSyn.IntSyn.cid list -> FunSyn.Pro
end (* Signature RELFUN *)       


