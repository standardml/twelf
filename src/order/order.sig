(* Termination Order *)
(* Author: Carsten Schuermann *)

signature ORDER =
sig

  structure IntSyn : INTSYN

  exception Error of string

  datatype 'a Order =	       	        (* Orders                     *)
      Arg of 'a				(* O ::= x                    *)
    | Lex of 'a Order list              (*     | {O1 .. On}           *)
    | Simul of 'a Order list            (*     | [O1 .. On]           *)

  datatype Mutual =			(* Termination ordering       *)
      Empty				(* O ::= No order specified   *)
    | LE of IntSyn.cid * Mutual		(*     | mutual dependencies  *)
    | LT of IntSyn.cid * Mutual		(*     | lex order for  -     *)

  datatype TDec =			(* Termination declaration *)
      TDec of int Order * Mutual

  val reset : unit -> unit
  val install : IntSyn.cid * TDec -> unit 
  val selLookup : IntSyn.cid -> int Order
  val mutLookup : IntSyn.cid -> Mutual
  val closure : IntSyn.cid -> IntSyn.cid list

end;  (* signature ORDER *)
