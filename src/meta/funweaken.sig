(* Weakening substitutions for meta substitutions *)
(* Author: Carsten Schuermann *)

signature FUNWEAKEN = 
sig
  (*! structure FunSyn : FUNSYN !*)

  val strengthenPsi : (FunSyn.lfctx * IntSyn.Sub) 
                  -> (FunSyn.lfctx * IntSyn.Sub)
  val strengthenPsi': (FunSyn.LFDec list * IntSyn.Sub) 
                  -> (FunSyn.LFDec list * IntSyn.Sub) 
end (* signature FUNWEAKEN *)