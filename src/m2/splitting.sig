(* Splitting *)
(* Author: Carsten Schuermann *)

signature SPLITTING = 
sig
  structure MetaSyn : METASYN

  exception Error of string

  type operator
    
  val expand : MetaSyn.State -> operator list 
  val apply : operator -> MetaSyn.State list

  val var : operator -> int
  val menu : operator -> string
  val index : operator -> int
end;  (* signature SPLITTING *)
