(* State for Proof Search *)
(* Author: Carsten Schuermann *)

functor StateSyn (structure IntSyn : INTSYN
		  structure FunSyn' : FUNSYN
		    sharing FunSyn'.IntSyn = IntSyn)
  : STATESYN =
struct
  structure FunSyn = FunSyn'
    
  datatype Order =	       	        (* Orders                     *)
    Arg of IntSyn.Exp		       	(* O ::= x                    *)
  | Lex of Order list			(*     | (O1 .. On)           *)
  | Simul of Order list			(*     | {O1 .. On}           *)
  | All of IntSyn.Dec * Order		(*     | {{D}} O              *)
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
           * Order			(* Current Order *)
           * (int * Order) list		(* History of Inductive calls (part of theorem, arguments) *)
           * FunSyn.For			(* Formula *)

  local
    structure F = FunSyn
    structure I = IntSyn  
     
    fun orderSub (Arg U, s) = Arg (I.EClo (U, s))
      | orderSub (Lex Os, s) = Lex (map (fn O => orderSub (O, s)) Os)
      | orderSub (Simul Os, s) = Simul (map (fn O => orderSub (O, s)) Os)
      (* by invariant: no case for All and And *)


    (* decrease T = T'

       Invariant:
       T is either an Assumption or Induction tag
       T' = T - 1
    *)
    fun decrease (Assumption k) = Assumption (k-1)
      | decrease (Induction k) = Induction k

  in
    val orderSub = orderSub
    val decrease = decrease
  end (* local *)
end; (* signature STATESYN *)