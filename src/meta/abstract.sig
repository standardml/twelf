(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature MTPABSTRACT =
sig
  structure IntSyn : INTSYN

  exception Error of string
    
  val abstractSub : IntSyn.Sub  -> (IntSyn.dctx * IntSyn.Sub)
end;  (* signature MTPABSTRACT *)
