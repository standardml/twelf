(* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

signature FUNTYPECHECK = 
sig
  structure FunSyn : FUNSYN

  exception Error of string

  val check : FunSyn.Pro * FunSyn.For -> unit    
end (* Signature FUNTYPECHECK *)       

