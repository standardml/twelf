(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

signature STATESYN =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)

  datatype Order =	       	        (* Orders                     *)
    Arg of (IntSyn.Exp * IntSyn.Sub) * 
           (IntSyn.Exp * IntSyn.Sub)	(* O ::= U[s] : V[s]          *)
  | Lex of Order list			(*     | (O1 .. On)           *)
  | Simul of Order list			(*     | {O1 .. On}           *)
  | All of IntSyn.Dec * Order  	(*     | {{D}} O              *)
  | And of Order * Order		(*     | O1 ^ O2              *)


  datatype Info =
    Splits of int
  | RL 
  | RLdone
    
  datatype Tag = 
    Parameter of FunSyn.label option
  | Lemma of Info
  | None

  datatype State =			(* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int			(* Part of theorem                   *)
	   * (IntSyn.dctx	(* Context of Hypothesis, in general not named *)
           * Tag IntSyn.Ctx) (* Status information *)
           * (FunSyn.For * Order)	(* Induction hypothesis, order       *)
           * int			(* length of meta context            *)
           * Order			(* Current order *)
           * (int * FunSyn.For) list	(* History of residual lemmas *)
           * FunSyn.For			(* Formula *)

  val orderSub : Order * IntSyn.Sub -> Order  
  val decrease : Tag -> Tag
  val splitDepth : Info -> int

  val normalizeOrder : Order -> Order
  val convOrder : Order * Order -> bool

  val normalizeTag : Tag * IntSyn.Sub -> Tag
end; (* signature STATESYN *)