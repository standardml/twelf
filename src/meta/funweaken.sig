(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

signature FUNWEAKEN = 
sig
  structure FunSyn : FUNSYN

  val strengthenPsi : (FunSyn.lfctx * FunSyn.IntSyn.Sub) 
                  -> (FunSyn.lfctx * FunSyn.IntSyn.Sub)
  val strengthenPsi': (FunSyn.LFDec list * FunSyn.IntSyn.Sub) 
                  -> (FunSyn.LFDec list * FunSyn.IntSyn.Sub) 
end (* signature FUNWEAKEN *)