(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPRINT =
sig
  structure Formatter : FORMATTER
  structure StateSyn : STATESYN

  exception Error of string 

  val nameState : StateSyn.State -> StateSyn.State
  val formatState : StateSyn.State -> Formatter.format 
  val stateToString : StateSyn.State -> string
end;  (* signature MTPRINT *)
