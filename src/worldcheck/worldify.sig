(* Worldify *) 
(* Author: Carsten Schuermann *)


signature WORLDIFY = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string 

  val worldify :  IntSyn.cid -> IntSyn.ConDec list
  val worldifyGoal : IntSyn.Dec IntSyn.Ctx * IntSyn.Exp -> IntSyn.Exp
end; (* signature WORLDIFY *)
