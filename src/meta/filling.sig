(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPFILLING = 
sig
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : StateSyn.State -> operator 
  val apply : operator -> (int * FunSyn.Pro)
  val menu : operator -> string
end; (* signature MTPFILLING *)


