(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature ABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string

  val piDepend  : (IntSyn.Dec * IntSyn.Depend) * IntSyn.Exp -> IntSyn.Exp
  val closedDec : IntSyn.Dec IntSyn.Ctx * (IntSyn.Dec * IntSyn.Sub) -> bool
  val closedSub : IntSyn.Dec IntSyn.Ctx * IntSyn.Sub -> bool
  val closedExp : IntSyn.Dec IntSyn.Ctx * (IntSyn.Exp * IntSyn.Sub) -> bool

  val abstractDecImp : IntSyn.Exp  -> (int * IntSyn.Exp)
  val abstractDef : (IntSyn.Exp * IntSyn.Exp) -> 
                       (int * (IntSyn.Exp * IntSyn.Exp))

  val collectEVars : IntSyn.dctx * IntSyn.eclo * IntSyn.Exp list -> IntSyn.Exp list

end;  (* signature ABSTRACT *)
