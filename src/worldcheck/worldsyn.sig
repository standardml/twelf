(* World Checking *) 
(* Author: Carsten Schuermann *)


signature WORLDSYN = 
sig
  structure IntSyn : INTSYN

  exception Error of string 

  type dlist = IntSyn.Dec list

  (*
  datatype LabelDec =			(* ContextBody                 *)
    LabelDec of string * dlist * dlist	(* B ::= l : SOME L1. BLOCK L2 *)
					
  datatype World =			(* Worlds                      *)
    Closed				(* W ::= .                     *)
  | Schema of World * LabelDec          (*     | W, B                  *)
  *)

  datatype Worlds = Worlds of IntSyn.cid list

  val reset : unit -> unit
  val install : IntSyn.cid * Worlds -> unit
  val lookup : IntSyn.cid -> Worlds      (* raises Error if undeclared *)

  val worldcheck : Worlds -> IntSyn.cid -> unit
  val ctxToList : IntSyn.Dec IntSyn.Ctx -> dlist

end; (* signature WORLDSYN *)
