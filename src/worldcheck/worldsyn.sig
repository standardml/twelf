(* World Checking *) 
(* Author: Carsten Schuermann *)


signature WORLDSYN = 
sig
  structure IntSyn : INTSYN

  exception Error of string 

  type label = int      
  type name = string
  type lemma = int 

  type dlist = IntSyn.Dec list

  datatype LabelDec =			(* ContextBody                *)
    LabelDec of name * dlist * dlist    (* LD = SOME G1. BLOCK G2     *)
					
  datatype World =			(* Worlds                     *)
    Closed				(* W ::= .                    *)
  | Schema of World * LabelDec          (*     | W, l : LD            *)

  val worldcheck : World -> IntSyn.cid -> unit
  val ctxToList : IntSyn.Dec IntSyn.Ctx -> dlist
end; (* signature WORLDSYN *)
