(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGACOVERAGE = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string

  val coverageCheckPrg : Tomega.Worlds * Tomega.Dec IntSyn.Ctx * Tomega.Prg -> unit
end (* Signature TOMEGACOVERAGE *)       

