(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature MTPABSTRACT =
sig
  structure IntSyn : INTSYN
  structure StateSyn : STATESYN

  exception Error of string
    
  val abstractSub : IntSyn.Sub * StateSyn.SplitTag IntSyn.Ctx 
        -> ((IntSyn.dctx * StateSyn.SplitTag IntSyn.Ctx) * IntSyn.Sub)
end;  (* signature MTPABSTRACT *)
