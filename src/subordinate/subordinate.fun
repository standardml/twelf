(* Subordination a la Virga [Technical Report 96] *)
(* Author: Carsten Schuermann *)

functor Subordinate (structure Global : GLOBAL
		     structure IntSyn': INTSYN
		     structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn')
  : SUBORDINATE =
struct
  structure IntSyn = IntSyn'
 
  local
    structure I = IntSyn

    (* Subordination array

       Definition:
       soArray is valid 
       iff For all b:
           If   soArray (b) = BL,BR
           then for all a:K
                a < b iff a in BL
		(a is subordinate to b)
           and  for all c:K
    	        b < c iff c in BR
		(b is subordinate to c)
	   where subordination is transitive but not necessarily
	   reflexive
    *)

    val soArray : (IntSyn.cid list * IntSyn.cid list) Array.array    
        = Array.array (Global.maxCid + 1, (nil, nil)) 

    (* reset () = ()

       Effect: Empties soArray
    *)
    fun reset () = Array.modify (fn _ => (nil, nil)) soArray

    (* a < b = B'

       Invariant:
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a is transitively subordinated by b
    *)
    fun below (a, b) =
	let 
	  val (BL, BR) = Array.sub (soArray, b)
	in
	  List.exists (fn x => x = a) BL
	end

    (* a <* b = B'

       Invariant:
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a is transitively and reflexively subordinated by b
    *)
    fun belowEq (a, b) = (a = b) orelse below (a, b)

    (* a == b = B'

       Invariant:
       If   Sigma (a) = K1 and  Sigma (b) = K2
       then B' = true :iff a <* b and b <* a
    *)
    fun equiv (a, b) = belowEq (a, b) andalso belowEq (b, a)

    (* merge (L1, L2) = L'
     
       Invariant: 
       L' is shortest list s.t.
       L1 subset L' and L2 subset L'
    *)
    fun merge (nil, L2) = L2 
      | merge (a :: L1, L2) =
        if List.exists (fn x => x = a) L2
	  then merge (L1, L2)
	else merge (L1, a :: L2)

    (* mergeLeft (a, R, seen) = seen'

       Effect: updates the soArray to record that a is subordinate
               to every type family in R and, transitively, every
	       a' which is subordinate to a is also subordinate
	       to R.

               seen is maintained for termination and contains
	       those families a' such that a' < R has already
	       been recorded.
    *)
    fun mergeLeft (a, R, seen) = 
        let 
	  val (AL, AR) = Array.sub (soArray, a) 
	in
	  (Array.update (soArray, a, (AL, merge (AR, R)));
	   mergeLeftList (AL, R, a::seen))
	end

    and mergeLeftList (nil, R, seen) = seen
      | mergeLeftList (a::AL, R, seen) = 
        if List.exists (fn x => x = a) seen
	  then mergeLeftList (AL, R, seen)
	else mergeLeftList (AL, R, mergeLeft (a, R, seen))

    (* mergeRight (L, b, seen) = seen'

       Effect: updates the soArray to record that b subordinates
               every type family in L and, transitively, every
	       b' which subordinates b also subordinates L.

               seen is maintained for termination and contains
	       those families b' such that L < b' has already
	       been recorded.
    *)
    fun mergeRight (L, b, seen) = 
      let 
	val (BL, BR) = Array.sub (soArray, b) 
      in
	(Array.update (soArray, b, (merge (L, BL), BR));
	 mergeRightList (L, BR, b::seen))
      end

    and mergeRightList (L, nil, seen) = seen
      | mergeRightList (L, b::BR, seen) = 
	if List.exists (fn x => x = b) seen
	  then mergeRightList (L, BR, seen)
	else mergeRightList (L, BR, mergeRight (L, b, seen))

    (* transClosure (a, b) = ()

       Invariant:
       If   soArray is valid
       then soArray is updated according to the information a < b
       and  soArray is still valid
    *)
    fun transClosure (a, b) = 
	if below (a, b) then ()
	else 
	  let 
	    val (AL, AR) = Array.sub (soArray, a) 
	    val (BL, BR) = Array.sub (soArray, b)
	  in
	    (mergeLeft (a, b :: BR, nil); mergeRight (a :: AL, b, nil); ())
	  end

    (* installKind (V, a) = ()
 
       Invariant:
       If   G |- V : L and V in nf
       and  a = targetFam V
       and  soArray is valid
       then soArray is updated according to all dependencies in V
       and  soArray is valid
    *)
    fun installKind (I.Uni L, a) = ()
      | installKind (I.Pi ((I.Dec (_, V1), P), V2), a) =
          (transClosure (I.targetFam V1, a);
	   installKind (V2, a))

    (* Passing around substitutions and calling whnf below is
       redundant, since the terms starts in normal form and
       we only refer to the target families.
    *)

    (* inferExp (G, (U1, s1), (V2, s2)) = ()

       Invariant: 
       If   G  |- s1 : G1, and G1 |- U1 : V1
       and  G  |- s2 : G2, and G2 |- V2 : L
       and  G  |- V1[s1] = V2[s2] : L
       and  soArray valid	 
       then soArray is updated accorindg to all dependencies in U1[s1]
       and  soArray is valid
    *)
    fun installExp (G, Us, Vs) = installExpW (G, Whnf.whnf Us, Whnf.whnf Vs)
    and installExpW (G, (I.Uni (L), _), _) = ()
      | installExpW (G, (I.Pi ((D as I.Dec (_, V1), _) , V2), s), 
		        (I.Uni I.Type, t)) = 
          (transClosure (I.targetFam V1, I.targetFam V2);
	   installExpW (G, (V1, s), (I.Uni I.Type, t));
	   installExpW (I.Decl (G, I.decSub (D, s)), (V2, I.dot1 s), 
				(I.Uni I.Type, t)))
      | installExpW (G, (I.Root (C, S), s), _) =
	  installSpine (G, (S, s), Whnf.whnf (inferCon (G, C), I.id))
      | installExpW (G, (I.Lam (D1 as I.Dec (_, V1), U), s) , 
		     (I.Pi ((D2 (* = D1 *), _), V2), t)) = 
	  (transClosure (I.targetFam V1, I.targetFam V2);
	   installExpW (G, (V1, s), (I.Uni I.Type, I.id));
	   installExpW (I.Decl (G, I.decSub (D1, s)), (U, I.dot1 s), 
			(V2, I.dot1 t)))
      | installExpW (G, (I.FgnExp (cs, ops), s), Vs) =
          installExpW (G, (#toInternal(ops) (), s), Vs)

    (* inferSpine (G, (S, s1), (V2, s2)) = ()

       Invariant: 
       If   G  |- s1 : G1, and G1 |- S : V1 > V1'
       and  G  |- s2 : G2, and G2 |- V2 : L
       and  G  |- V1[s1] = V2[s2] : L
       and  soArray valid	 
       then soArray is updated accorindg to all dependencies in U1[s1]
       and  soArray is valid
     *)
    and installSpine (G, (I.Nil, _), Vs) = ()
      | installSpine (G, (I.SClo (S, s'), s), Vs) = 
	  installSpine (G, (S, I.comp (s', s)), Vs)
      | installSpine (G, (I.App (U, S), s1), 
		      (I.Pi ((I.Dec (_, V1), _), V2), s2)) =
	  (installExp (G, (U, s1), (V1, s2));
	   installSpine (G, (S, s1), 
			 Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))))

    (* inferCon (G, C) = V'

       Invariant: 
       If    G |- C : V  
       then  G |- V : L 
    *)
    and inferCon (G, I.BVar (k')) = 
	let 
	  val I.Dec (_,V) = I.ctxDec (G, k')
	in
	  V
	end
      | inferCon (G, I.Const(c)) = I.constType (c)
      | inferCon (G, I.Def(d))  = I.constType (d)
      | inferCon (G, I.Skonst(c)) = I.constType (c)
      | inferCon (G, I.FgnConst(cs, conDec)) = I.conDecType (conDec)

    (* install c = ()

       Invariant:
       If   soArray is valid
       and  c is a constant
       then soArray is updated accorindg to all dependencies in U1[s1]
       and  soArray is valid
    *)
    fun install c = 
      let 
	val V = I.constType c
      in
	case I.targetFamOpt V
	  of NONE => installKind (V, c)
	   | SOME a => installExp (I.Null, (V, I.id), (I.Uni I.Type, I.id))
      end

    (* weaken (G, a) = (w')
    *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) = 
        let 
	  val w' = weaken (G', a) 
	in
	  if belowEq (I.targetFam V, a) then I.dot1 w'
	  else I.comp (w', I.shift)
	end



  in
    val reset = reset
     
    val install = install

    val below = below
    val belowEq = belowEq
    val equiv = equiv

    val weaken = weaken

  end (* local *)
end; (* functor Subordinate *)
