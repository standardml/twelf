(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

signature STATESYN =
sig
  structure FunSyn : FUNSYN

  datatype Order =	       	        (* Orders                     *)
    Arg of FunSyn.IntSyn.Exp	        (* O ::= x                    *)
  | Lex of Order list			(*     | (O1 .. On)           *)
  | Simul of Order list			(*     | {O1 .. On}           *)
  | All of FunSyn.IntSyn.Dec * Order  	(*     | {{D}} O              *)
  | And of Order * Order		(*     | O1 ^ O2              *)
    

  datatype SplitTag = 
    Parameter
  | Lemma 
  | Assumption of int
  | Induction  of int

  datatype State =			(* S = <(G, B), (IH, OH), d, O, H, F> *)
    State of (FunSyn.IntSyn.dctx	(* Context of Hypothesis             *)
           * SplitTag FunSyn.IntSyn.Ctx) (* Status information *)
           * (FunSyn.For * Order)	(* Induction hypothesis, order       *)
           * int			(* length of meta context            *)
           * Order			(* Current order *)
           * (int * Order) list		(* History of Inductive calls (part of theorem, arguments) *)
           * FunSyn.For			(* Formula *)

  val orderSub : Order * FunSyn.IntSyn.Sub -> Order  
  val decrease : SplitTag -> SplitTag
end; (* signature STATESYN *)