(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string
    
  val raiseType : IntSyn.dctx * IntSyn.eclo -> IntSyn.Exp
  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool

  val abstractDec : IntSyn.Exp  -> (IntSyn.imp * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp) -> 
                       (IntSyn.imp * (IntSyn.Exp * IntSyn.Exp))
end;  (* signature ABSTRACT *)
