(* State for Proof Search *)
(* Author: Carsten Schuermann *)

functor StateSyn (structure IntSyn' : INTSYN
		  structure FunSyn' : FUNSYN
		    sharing FunSyn'.IntSyn = IntSyn'
		  structure Whnf : WHNF
		    sharing Whnf.IntSyn = IntSyn'
		  structure Conv : CONV
		    sharing Conv.IntSyn = IntSyn')
  : STATESYN =
struct
  structure IntSyn = IntSyn'
  structure FunSyn = FunSyn'
    
  datatype Order =	       	        (* Orders                     *)
    Arg of (IntSyn.Exp * IntSyn.Sub) * 
           (IntSyn.Exp * IntSyn.Sub)	(* O ::= U[s] : V[s]        *)
  | Lex of Order list			(*     | (O1 .. On)           *)
  | Simul of Order list			(*     | {O1 .. On}           *)
  | All of IntSyn.Dec * Order		(*     | {{D}} O              *)
  | And of Order * Order		(*     | O1 ^ O2              *)
    
  datatype SplitTag = 
    Parameter
  | Lemma 
  | Assumption of int
  | Induction  of int

  datatype State =			(* S = <n, (G, B), (IH, OH), d, O, H, F> *)
    State of int			(* Part of theorem                   *)
	   * (FunSyn.IntSyn.dctx		(* Context of Hypothesis             *)
           * SplitTag FunSyn.IntSyn.Ctx) (* Status information *)
           * (FunSyn.For * Order)	(* Induction hypothesis, order       *)
           * int			(* length of meta context            *)
           * Order			(* Current Order *)
           * (int * Order) list		(* History of Inductive calls (part of theorem, arguments) *)
           * FunSyn.For			(* Formula *)

  local
    structure F = FunSyn
    structure I = IntSyn  
     
    fun orderSub (Arg ((U, s1), (V, s2)), s) = Arg ((U,  I.comp (s1, s)), (V, I.comp (s2, s)))
      | orderSub (Lex Os, s) = Lex (map (fn O => orderSub (O, s)) Os)
      | orderSub (Simul Os, s) = Simul (map (fn O => orderSub (O, s)) Os)
      (* by invariant: no case for All and And *)


    fun normalizeOrder (Arg (Us, Vs)) = Arg ((Whnf.normalize Us, I.id), 
					     (Whnf.normalize Vs, I.id))
      | normalizeOrder (Lex Os) = Lex (map normalizeOrder Os)
      | normalizeOrder (Simul Os) = Simul (map normalizeOrder Os)
      (* by invariant: no case for All and And *)

    fun convOrder (Arg (Us1, _), Arg (Us2, _ )) = Conv.conv (Us1, Us2)
      | convOrder (Lex Os1, Lex Os2) = convOrders (Os1, Os2)
      | convOrder (Simul Os1, Simul Os2) = convOrders (Os1, Os2)
    and convOrders (nil, nil) = true
      | convOrders (O1 :: L1, O2 :: L2) = 
          convOrder (O1, O2) andalso convOrders (L1, L2)
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
    val normalizeOrder = normalizeOrder
    val convOrder = convOrder
  end (* local *)
end; (* signature STATESYN *)