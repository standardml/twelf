(* Abstraction mechanisms form programs and formulas *)
(* Author: Carsten Schuermann *)

signature TOMEGAABSTRACT = 
sig
  exception Error of string
  val raiseFor : IntSyn.Dec IntSyn.Ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
  val raisePrg : IntSyn.Dec IntSyn.Ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseP   : IntSyn.Dec IntSyn.Ctx * Tomega.Prg * Tomega.For -> Tomega.Prg
  val raiseF   : IntSyn.Dec IntSyn.Ctx * (Tomega.For * IntSyn.Sub) -> Tomega.For
end (* Signature TOMEGAABSTRACT *)       

