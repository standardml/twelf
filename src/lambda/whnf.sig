(* Weak Head-Normal Forms *)
(* Authors: Frank Pfenning, Carsten Schuermann *)

signature WHNF =
sig

  structure IntSyn : INTSYN

  val whnf : IntSyn.eclo -> IntSyn.eclo
  val expandDef : IntSyn.eclo -> IntSyn.eclo
  val etaExpandRoot : IntSyn.Exp -> IntSyn.Exp
  val whnfEta : (IntSyn.eclo * IntSyn.eclo) -> (IntSyn.eclo * IntSyn.eclo)

  val normalize: IntSyn.eclo -> IntSyn.Exp
  val normalizeDec: IntSyn.Dec * IntSyn.Sub -> IntSyn.Dec
  val normalizeCtx: IntSyn.dctx -> IntSyn.dctx

end; (* signature WHNF *)
