(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature MTPABSTRACT =
sig
  structure IntSyn : INTSYN
  structure StateSyn : STATESYN

  exception Error of string


  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.Sub
  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp 
      
  val abstractSub : IntSyn.Sub * (IntSyn.dctx * StateSyn.Tag IntSyn.Ctx) * IntSyn.Sub * StateSyn.Tag IntSyn.Ctx
        -> ((IntSyn.dctx * StateSyn.Tag IntSyn.Ctx) * IntSyn.Sub)
  val abstractSub' : (IntSyn.dctx * StateSyn.Tag IntSyn.Ctx) * IntSyn.Sub * StateSyn.Tag IntSyn.Ctx
        -> ((IntSyn.dctx * StateSyn.Tag IntSyn.Ctx) * IntSyn.Sub)

end;  (* signature MTPABSTRACT *)
