(* World Checking *) 
(* Author: Carsten Schuermann *)


signature WORLDSYN = 
sig
  structure IntSyn : INTSYN

  exception Error of string 

  type dlist = IntSyn.Dec list

  datatype LabelDec =			(* ContextBody                 *)
    LabelDec of string * dlist * dlist	(* B ::= l : SOME L1. BLOCK L2 *)
					
  datatype World =			(* Worlds                      *)
    Closed				(* W ::= .                     *)
  | Schema of World * LabelDec          (*     | W, B                  *)

  val reset : unit -> unit
  val install : IntSyn.cid * World -> unit

  val worldcheck : World -> IntSyn.cid -> unit
  val ctxToList : IntSyn.Dec IntSyn.Ctx -> dlist

end; (* signature WORLDSYN *)
