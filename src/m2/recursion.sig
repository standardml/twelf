(* Recursion *)
(* Author: Carsten Schuermann *)

signature RECURSION = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expandLazy : MetaSyn.State -> operator list 
  val expandEager : MetaSyn.State -> operator list 

  val apply : operator -> MetaSyn.State

  val menu : operator -> string
end;  (* signature RECURSION *)
