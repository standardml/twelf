(* Recurse: Version 1.4 *)
(* Author: Carsten Schuermann *)

signature RECURSE = 
sig
  structure State : STATE

  exception Error of string

  type operator

  val expand : State.State -> operator 
  val apply : operator -> State.State
  val menu : operator -> string
end; (* signature RECURSE *)


