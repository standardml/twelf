(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

signature STATEPRINT =
sig
  structure Formatter : FORMATTER

  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  structure State : STATE

  exception Error of string 

  val nameState : State.State -> State.State
  val formatState : State.State -> Formatter.format 
  val stateToString : State.State -> string
end;  (* signature STATEPRINT *)
