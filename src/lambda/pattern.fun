(* Pattern Substitutions *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Pattern (structure IntSyn' : INTSYN)
  : PATTERN = 
struct
  structure IntSyn = IntSyn'

  local 
    open IntSyn 

    (* checkSub s = B

       Invariant:
       If    G |- s : G' 
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k for all 1 <= i <= m
    *)
    fun checkSub (Shift(k)) = true
      | checkSub (Dot (Idx (n), s)) = 
          let fun checkBVar (Shift(k)) = (n <= k)
		| checkBVar (Dot (Idx (n'), s)) = 
	            n <> n' andalso checkBVar (s)
		| checkBVar _ = false
	  in
	    checkBVar s andalso checkSub s
	  end
      | checkSub _ = false

    exception Eta

    (* etaContract (U, s, n) = k'

       Invariant: 
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k 
	    then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
	    else Eta is raised
	      (even if U[s] might be eta-reducible to some other expressions).
    *)
    (* optimization(?): quick check w/o substitution first *)
    fun etaContract (Root (BVar(k), S), s, n) =
        (case bvarSub (k, s)
	   of Idx (k') => if k' > n
			    then (etaContract' (S, s, n); k'-n)
			  else raise Eta
	    | _ => raise Eta)
      | etaContract (Lam (D, U), s, n) =
	  etaContract (U, dot1 s, n+1)
      | etaContract (EClo (U, s'), s, n) =
	  etaContract (U, comp (s', s), n)
      | etaContract (EVar (ref (SOME(U)), _, _), s, n) =
	  etaContract (U, s, n)
      | etaContract _ = raise Eta
        (* Should fail: (c@S), (d@S), (F@S), X *)
        (* Not treated (fails): U@S *)
        (* Could weak head-normalize for more thorough checks *)
        (* Impossible: L, Pi D.V *)

    (* etaContract' (S, s, n) = R'

       Invariant:
       If  G |- s : G1    and  G1 |- S : V > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
	    then () 
       else Eta is raised
    *)
    and etaContract' (Nil, s, 0) = ()
      | etaContract' (App(U, S), s, n) =
          if etaContract (U, s, 0) = n
	    then etaContract' (S, s, n-1)
	  else raise Eta
      | etaContract' (SClo (S, s'), s, n) =
	  etaContract' (S, comp (s', s), n)
      | etaContract' _ = raise Eta

    (* dotEta (Ft, s) = s'
       
       Invariant: 
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
    fun dotEta (Ft as Idx _, s) = Dot (Ft, s)
      | dotEta (Ft as Exp (U, V), s) =
          let
	    val Ft' = Idx (etaContract (U, id, 0))
	             handle Eta => Ft
	  in
	    Dot (Ft', s)
	  end
 
  in
    val checkSub = checkSub
    val dotEta = dotEta
    exception Eta = Eta
    val etaContract = (fn U => etaContract (U, id, 0))
  end (* local *)
end; (* functor Pattern *)
