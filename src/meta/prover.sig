(* Meta Prover Version 1.3 *)
(* Author: Carsten Schuermann *)


signature MTPROVER =
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string 

  val init : FunSyn.For * StateSyn.Order -> unit
end;  (* signature MTPROVER *)
