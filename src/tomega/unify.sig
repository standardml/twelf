(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGAUNIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Unify of string

  val unifyFor : Tomega.Dec IntSyn.Ctx * Tomega.For * Tomega.For -> unit
end (* Signature TOMEGATYPECHECK *)       

