(* Filling: Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPFILLING = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.State -> operator 
  val apply : operator -> bool
  val menu : operator -> string
end; (* signature MTPFILLING *)


