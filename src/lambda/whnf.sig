(* Weak Head-Normal Forms *)
(* Authors: Frank Pfenning, Carsten Schuermann *)

signature WHNF =
sig
  (*! structure IntSyn : INTSYN !*)

  (* Patterns *)
  val isPatSub : IntSyn.Sub -> bool
  val makePatSub : IntSyn.Sub -> IntSyn.Sub option
  val dotEta   : IntSyn.Front * IntSyn.Sub -> IntSyn.Sub

  exception Eta
  val etaContract : IntSyn.Exp -> int	(* can raise Eta *)

  (* Weak head normalization *)
  val whnf : IntSyn.eclo -> IntSyn.eclo
  val expandDef : IntSyn.eclo -> IntSyn.eclo
  val whnfExpandDef : IntSyn.eclo -> IntSyn.eclo
  val etaExpandRoot : IntSyn.Exp -> IntSyn.Exp
  val whnfEta : (IntSyn.eclo * IntSyn.eclo) -> (IntSyn.eclo * IntSyn.eclo)
  val lowerEVar : IntSyn.Exp -> IntSyn.Exp

  val newLoweredEVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.Exp
  val newSpineVar : IntSyn.dctx * IntSyn.eclo -> IntSyn.Spine
  val spineToSub : IntSyn.Spine * IntSyn.Sub -> IntSyn.Sub

  (* Full normalization *)
  val normalize: IntSyn.eclo -> IntSyn.Exp
  val normalizeDec: IntSyn.Dec * IntSyn.Sub -> IntSyn.Dec
  val normalizeCtx: IntSyn.dctx -> IntSyn.dctx

  (* Inverting substitutions *)
  val invert : IntSyn.Sub -> IntSyn.Sub
  val strengthen: IntSyn.Sub * IntSyn.dctx -> IntSyn.dctx 
  val isId : IntSyn.Sub -> bool

  val cloInv : IntSyn.Exp * IntSyn.Sub -> IntSyn.Exp
  val compInv : IntSyn.Sub * IntSyn.Sub -> IntSyn.Sub
end; (* signature WHNF *)
