(* ELIM: Version 1.4 *)
(* Author: Carsten Schuermann *)

signature ELIM = 
sig
  structure State : STATE

  exception Error of string

  type operator

  val expand : State.Focus -> operator list 
  val apply : operator -> unit
  val menu : operator -> string
end; (* signature ELIM *)


