(* Weakening substitutions *)
(* Author: Carsten Schuermann *)

signature WEAKEN = 
sig
  (*! structure IntSyn : INTSYN !*)

  val strengthenExp : (IntSyn.Exp * IntSyn.Sub) -> IntSyn.Exp
  val strengthenSpine: (IntSyn.Spine * IntSyn.Sub) -> IntSyn.Spine
  val strengthenCtx : (IntSyn.dctx * IntSyn.Sub) -> (IntSyn.dctx * IntSyn.Sub)
  val strengthenDec : (IntSyn.Dec * IntSyn.Sub) -> IntSyn.Dec
  val strengthenSub : (IntSyn.Sub * IntSyn.Sub) -> IntSyn.Sub
end (* signature PRUNE *)