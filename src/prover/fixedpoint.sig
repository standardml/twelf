(* Splitting: Version 1.4 *)
(* Author: Carsten Schuermann *)

signature FIXEDPOINT = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  structure State : STATE

  exception Error of string

  type operator

  val expand : (State.Focus * Tomega.TC) -> operator
  val apply : operator -> unit
  val menu : operator -> string
end; (* signature Fixed Point *)


