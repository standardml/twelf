(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

signature TOMEGATYPECHECK = 
sig
  exception Error of string

  val checkCtx : Tomega.Dec IntSyn.Ctx -> unit
  val checkFor : Tomega.Dec IntSyn.Ctx * Tomega.For -> unit
  val checkPrg : Tomega.Dec IntSyn.Ctx * (Tomega.Prg * Tomega.For) -> unit    
  val checkSub : Tomega.Dec IntSyn.Ctx * Tomega.Sub * Tomega.Dec IntSyn.Ctx -> unit
end (* Signature TOMEGATYPECHECK *)       

