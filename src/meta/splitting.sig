(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPSPLITTING = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator
    
  val expand : StateSyn.State -> operator list 
  val applicable : operator -> bool
  val apply : operator -> StateSyn.State list
  val menu : operator -> string
  val index : operator -> int
  val lt : operator * operator -> bool
  val eq : operator * operator -> bool
  val le : operator * operator -> bool
end;  (* signature MTPSPLITTING *)
