(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Unify (structure IntSyn' : INTSYN
	       structure Whnf    : WHNF
	         sharing Whnf.IntSyn = IntSyn'
	       structure Pattern : PATTERN
	         sharing Pattern.IntSyn = IntSyn'
	       structure Trail : TRAIL
		 sharing Trail.IntSyn = IntSyn')
  : UNIFY =
struct
  structure IntSyn = IntSyn'
    
  exception Unify of string
  
  local
    open IntSyn

    exception NonInvertible

    (* intersection (s1, s2) = s'
       s' = s1 /\ s2 (see JICSLP'96)
       
       Invariant: 
       If   G |- s1 : G'    s1 patsub
       and  G |- s2 : G'    s2 patsub
       then G |- s' : G'' for some G''  
       and  s' patsub
    *)
    fun intersection (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) = 
 	  if (k1 = k2) then dot1 (intersection (s1, s2))
	  else comp (intersection (s1, s2), shift)
      | intersection (s1 as Dot _, Shift (n2)) =
	  intersection (s1, Dot (Idx (n2+1), Shift (n2+1)))
      | intersection (Shift (n1), s2 as Dot _) = 
	  intersection (Dot (Idx (n1+1), Shift (n1+1)), s2)
      | intersection (Shift _ , Shift _) = id
        (* both substitutions are the same number of shifts by invariant *)
      (* all other cases impossible for pattern substitutions *)

    (* invertible (k, s) = B

       Invariant:
       If   G |- k : V
       and  G |- s : G'  and s patsub
       then B iff exists k' s.t. k'[s] = k
                  and G' |- k' : V'
    *) 
    fun invertible (k, s) =
        let
	  fun invertible' (Shift (n)) = k > n
	    | invertible' (Dot (Idx (k'), s')) = 
	      if k = k' then true 
	      else invertible' (s')
	in 
	  invertible' s
	end

    (* pruneSub (s1, s2) = s'
       s.t. s' = s1 | s2  (see JICSLP'96)
       where (s' o s1) o inv(s2) exists

       Invariant: 
       If   G  |- s1 : G1  and s1 patsub
       and  G  |- s2 : G2  and s2 patsub
       then G1 |- s' : G1' for some G1'
       and  s' is pat sub

       Effects: None (cannot raise Unify, instantiate, or affect constraints).

       Possible optimization: calculate ((s1 | s2) o s1) o inv (s2) simultaneously
       Possible optimization (here and elsewhere):
        unfold recursive call after expansion of substitution
    *)
    fun pruneSub (Dot (Idx (k1), s1), s2) = 
        if invertible (k1, s2) then dot1 (pruneSub (s1, s2))
	else comp (pruneSub (s1, s2), shift)
      | pruneSub (s1 as Shift (n), s2 as Dot (Idx (k), s2')) = 
	if n >= k then pruneSub (s1, s2')
	else pruneSub (Dot (Idx (n+1), Shift(n+1)), s2)
      | pruneSub (Shift(n1), s2 as Shift(n2)) =
	if n1 < n2 
	  then pruneSub (Dot (Idx (n1+1), Shift (n1+1)), s2)
	else id

    (* unifyUni (L1, L2) = ()
       raises Unify if universe L1 <> L2
    *)
    fun unifyUni (Type, Type) = ()
      | unifyUni (Kind, Kind) = ()
      | unifyUni _ = raise Unify "Universe level mismatch"

    (* tryInvertExpW  ((U, s1), s2, rOccur) = U'

       Invariant: 
       If   G  |- s1 : G1    G1 |- U : V             (U,s1)  in whnf
       and  G  |- s2 : G2                            s2 patsub
       and  rOccur does not occur in U
       then      G2 |- U' : V'
            and  G  |- V [s1] = V' [s2] = V'' : L
            and  G  |- U [s1] = U' [s2] : V'' 
       else exception NonInvertible is raised

       Other effects:  EVars in U might be instantiated by lowering
                       No instantiation due to pruning
		       No new constraints
    *)
    fun tryInvertExpW ((U as Uni(L), s1), s2, _) = U
      | tryInvertExpW ((Pi (DP1, U1), s1), s2, rOccur) = 
          Pi (tryInvertDecP((DP1,s1), s2, rOccur), tryInvertExp ((U1, dot1 s1), dot1 s2, rOccur))
      | tryInvertExpW ((Root (H, S), s1), s2, rOccur) =
	  Root (tryInvertHead (H, s2, rOccur), tryInvertSpine ((S, s1), s2, rOccur)) 
      | tryInvertExpW ((Lam (D1, U1), s1), s2, rOccur) = 
          Lam (tryInvertDec((D1,s1), s2, rOccur), tryInvertExp ((U1, dot1 s1), dot1 s2, rOccur))
      | tryInvertExpW ((U as EVar (r, V, _), s1), s2, rOccur) =
	  (* r = ref NONE *)
	  if (rOccur = r) then raise NonInvertible    (* occurs check implies non-invertibility *)
	  else EClo(U, tryInvertSub (s1, s2, rOccur)) (* might raise NonInvertible *)
      (* other cases impossible since (U,s1) whnf *)

    (* tryInvertExp ((U1, s1), s2, rOccur) = U'
       as in tryInvertExpW, except that (U,s1) may not be in whnf 
    *)
    and tryInvertExp (Us1, s2, rOccur) = tryInvertExpW (Whnf.whnf Us1, s2, rOccur)

    (* tryInvertVar (k, s) = k'
       s.t. k' [s] = k, raises NonInvertible if no such k' exists

       Invariant: 
       If   G  |- k : V    
       and  G  |- s : G1         s is a pattern substitution
       then      G1 |- V' : L         (for some level)
            and  G1 |- k' : V'           
            and  G  |- V  = V' [s] : L
            and  G  |- k  = k' [s] : V
       raises NonInvertible if no such k' exists
       Other effects: None
    *)
    and tryInvertVar (k, s) =
          let fun tryInvertVar' (Dot (Idx (k'), s'), j) = 
	            if k = k' then j+1
		    else tryInvertVar' (s', j+1)
		| tryInvertVar' (Shift(n), j) =
		    if k > n then k-n+j
		    else raise NonInvertible
	  in 
	    tryInvertVar' (s, 0) 
	  end

    (* tryInvertHead (H, s, rOccur) = H'
       s.t. H' [s] = H  and  rOccur not in H, otherwise raises NonInvertible

       Invariant: 
       If   G  |- H : V    
       and  G  |- s : G1         s is a pattern substitution
       and  rOccur does not occur in H
       then      G1 |- V' : L         (for some level)
            and  G1 |- H' : V'           
            and  G  |- V  = V' [s] : L
            and  G  |- H  = H' [s] : V
       raises NonInvertible if no such H' exists
       Other effects: might lower EVars
    *)
    and tryInvertHead (BVar (k), s, _) = BVar (tryInvertVar (k, s))
      | tryInvertHead (H as Const _, s, _) = H
      | tryInvertHead (H as Def _, s, _) = H
      | tryInvertHead (FVar (x, V, s'), s, rOccur) = 
          (tryInvertExp ((V, id), id, rOccur); FVar(x, V, tryInvertSub (s', s, rOccur)))
        (* tryInvertSub (s', s) always exists since s' = ^|G| *)

    (* tryInvertFront (Ft, s2, rOccur) = Ft'
       s.t. Ft  = Ft' [s2] and rOccur not in Ft, otherwise raises NonInvertible

       Invariant:
       If   G  |- Ft : V
       and  G  |- s2 : G2 
       and  rOccur does not occur in Ft
       then      G2 |- V' : L     (for some level L)
	    and  G2 |- Ft' : V'
	    and  G  |- V  = V' [s2] : L   
	    and  G  |- Ft  = Ft' [s2] : V       
       
       Effects: might lower EVars
    *)
    and tryInvertFront (Idx (k), s2, rOccur) = 
          Idx (tryInvertVar (k, s2))
      | tryInvertFront (Exp (U, V), s2, rOccur) =
	  Exp (tryInvertExp ((U, id), s2, rOccur), V)
        (* Case of arbitrary fronts:
           We have G |- (U:V).s1 : G1,V
	   hence   G |- s1 : G1   and  G |- U : V [s1]
	   If the inverse of s2 exists we obtain
	           G2 |- s1 o inv(s2) : G1
	   and     G2 |- (U [inv(s2)]:V) [s1 o inv(s2)]
	   hence   G2 |- (U [inv(s2)]:V).(s1 o inv(s2)) : G1, V
	*)

    (* tryInvertSpine ((S, s1), s2, rOccur) = S'
       s.t. S'[s2] = S [s1]  and  rOccur not in S, otherwise raises NonInvertible

       Invariant: 
       If   G  |- s1 : G1    G1 |- S : V > W
       and  G  |- s2 : G2 
       and  rOccur does not occur in S
       then      G  |- S' : V' > W'
            and  G  |- V [s1] = V' [s2] = V'' : L    for some level L
            and  G  |- W [s1] = W' [s2] = W'' : L    
            and  G  |- S [s1] = S' [s2] : V'' > W'' 
       raises NonInvertible if no such S' exists
       Other effects: instantiation of EVars by lowering 
                      No instantiation due to pruning or new constraints
    *)
    and tryInvertSpine ((Nil, s1), s2, rOccur) = Nil
      | tryInvertSpine ((App (U, S), s1), s2, rOccur) = 
	  App(tryInvertExp ((U, s1), s2, rOccur), 
	      tryInvertSpine ((S, s1), s2, rOccur))
      | tryInvertSpine ((SClo(S, s1'), s1), s2, rOccur) =
	  tryInvertSpine ((S, comp (s1', s1)), s2, rOccur)

    (* tryInvertSub (s1, s2, rOccur) = s'
       s.t s1 = s' o s2, raises NonInvertible if no such s' exists

       Invariant: 
       If   G  |- s1 : G1      (s1 not patsub)
       and  G  |- s2 : G2  and s2 patsub
       and  rOccur does not occur in s1
       then      G2 |- s' : G1  and s' patsub
            and  s1 = s' o s2
	    and  s' is patsub
       raises NonInvertible is no such s' exists
       Other effects: possible instantiation of EVars by lowering
                      No instantiation due to pruning
		      No new constraints
    *)
    and tryInvertSub (Shift (n1), s2 as Shift (n2), rOccur) =
          if n1 < n2 
	    then raise NonInvertible
	      (* next line always fails --- raise NonInvertible instead -fp *)
	      (* Sun May  3 10:01:18 1998 *)
	      (* tryInvertSub (Dot (Idx (n1+1), Shift(n1+1)), s2, rOccur) *)
	  else Shift (n1-n2)
      | tryInvertSub (s1 as Shift (n), s2 as Dot (Idx (k), s2'), rOccur) =
	(* fixed bug below  Mon Aug 31 10:38:47 1998 -fp *)
	if n >= k
          then comp (tryInvertSub (s1, s2', rOccur), shift)
	else tryInvertSub (Dot (Idx (n+1), Shift (n+1)), s2, rOccur)
      | tryInvertSub (Dot (Ft, s1), s2, rOccur) =
	  Dot (tryInvertFront (Ft, s2, rOccur), tryInvertSub (s1, s2, rOccur))

    (* tryInvertDec ((D,s1), s2, rOccur) see tryInvertExp *)
    and tryInvertDec ((Dec (name, V), s1), s2, rOccur) =
          Dec (name, tryInvertExp ((V, s1), s2, rOccur)) 

    (* tryInvertDecP see tryInvertDec *)
    and tryInvertDecP (((D, P), s1), s2, rOccur) =
          (tryInvertDec ((D, s1), s2, rOccur), P)

    (* safeInvertExp ((U, s1), s2) = U' s.t. U'[s2] = U[s1]

       Assumes U' exists (raises uncatchable NonInvertible otherwise)
       No effects except possible lowering of EVars.
       
       For details see tryInvertExp
    *)
    (* improvement: use one reference, instead of creating a new one for every call -fp *)
    fun safeInvertExp (Us1, s2) = tryInvertExp (Us1, s2, ref NONE)

    (* Instantiating EVars *)
    (* Awaken constraints associated with X identified by r *)
    fun instantiateEVarC (r, U, Cnstr) = 
        let
	  fun awaken nil = ()
	    | awaken (Eqn (EClo Us1, EClo Us2)::Cnstr) =
	      (unifyExp (Us1, Us2) ; awaken Cnstr)
	in
	  Trail.instantiateEVar(r,U);
	  awaken Cnstr
	end

    (* Inverting substitutions *)

    (* invertExpW  ((U, s1), s2, rOccur) = (U[s1])[s2]-1 = U'

       Invariant: 
       If   G  |- s1 : G1    G1 |- U : V    (U,s1)  in whnf
       and  G  |- s2 : G2                   s2 patsub
       and  G  |- (V[s1]) [s2]-1  and  G[s2]-1 = G2  exist
       and  rOccur does not occur in G or V[s1]
       then
       if  rOccur does not occur in rigid position in U
       and there is a U' such that
                 G2 |- U' : V'
            and  G  |- V [s1] = V' [s2] = V'' : L         for some level L
            and  G  |- U [s1] = U' [s2] : V'' 
       then U' is returned
       else exception Unify is raised

       Other effects:  EVars in U might be instantiated by lowering or pruning
                       Constraints may be added for non-patterns.

       Note that the invariants on G[s2]-1 and V[s2]-1 require that the inverse
       is calculated left-to-right.
    *) 
    and invertExpW ((U as Uni(L), s1), s2, _) = 
          U
      | invertExpW ((Pi (DP1, U1), s1), s2, rOccur) = 
          Pi (invertDecP ((DP1,s1), s2, rOccur), invertExp ((U1, dot1 s1), dot1 s2, rOccur))
      | invertExpW ((Root (H, S), s1), s2, rOccur) =
	  Root (invertHead (H, s2, rOccur), invertSpine ((S, s1), s2, rOccur)) 
      | invertExpW ((Lam (D1, U1), s1), s2, rOccur) = 
          Lam (invertDec((D1,s1), s2, rOccur), invertExp ((U1, dot1 s1), dot1 s2, rOccur))
      | invertExpW ((U as EVar (r, V, Cnstr), s1), s2, rOccur) =
	  (* r = ref NONE *)
	  if (rOccur = r) then raise Unify "Variable occurrence"
	  else if Pattern.checkSub(s1)
		 then let
			val s1' = pruneSub (s1, s2)
			val V' = invertExp ((V, id), s1', rOccur)
			(* Always exists by invariant on G and V[s1] *)
			val U' = newEVar(V')
		      in
			(instantiateEVarC (r, EClo (U', s1'), Cnstr);
			 EClo (U', invertSub (comp (s1', s1), s2))) (* always succeeds *)
		      end
	       else (* s1 not patsub *)
		 EClo(U, tryInvertSub (s1, s2, rOccur))
		 handle NonInvertible => 
		   let 
		     val U' = newEVar (invertExp ((V, s1), s2, rOccur))
		     (* G2 |- U' : V'
		        G2 |- V' : L 
			G  |- V' [s2] = V [s1] 
			V' always exists by invariant on G and V[s1]
		     *)
		   in
  		     Trail.instantiateEVar (r, newEVarCnstr (V, (Eqn (EClo (U, s1),
								      EClo (U', s2)))
							     :: Cnstr));
		     (* new constraint : U [s1] = U' [s2] *)
                     (* use Trail.inst... to skip over constraint activation -jp *)
		     U'
		   end
      (* other cases impossible since (U,s1) whnf *)

    (* invertExp ((U1, s1), s2, rOccur) = U'
       as in invertExpW, except that arguments may not be in whnf 
    *)
    and invertExp (Us1, s2, rOccur) = invertExpW (Whnf.whnf Us1, s2, rOccur)

    (* invertVar (k, s) = k'
       s.t. k' [s] = k, raises Unify if no such k' exists

       Invariant: 
       If   G  |- k : V    
       and  G  |- s : G1         s patsub
       then      G1 |- V' : L
            and  G1 |- k' : V'           
            and  G  |- V  = V' [s] : L
            and  G  |- k  = k' [s] : V
       raises Unify if no such k' exists
       Other effects: None
    *)
    and invertVar (k, s) =
        let fun invertVar' (Dot (Idx (k'), s'), j) = 
	        if k = k' then j+1
		else invertVar' (s', j+1)
	      | invertVar' (Shift(n), j) =
		if k > n then k-n+j
		else raise Unify ("Parameter dependency")
	in 
	  invertVar' (s, 0) 
	end

    (* invertHead (H, s, rOccur) = H'
       s.t. H' [s] = H  and  rOccur not in H, otherwise raises Unify

       Invariant: 
       If   G  |- H : V    
       and  G  |- s : G1         s patsub
       then
       if  rOccur does not occur in rigid position in H 
       and       G1 |- V' : L
            and  G1 |- H' : V'           
            and  G  |- V  = V' [s] : L
            and  G  |- H  = H' [s] : V
       then return H'
       else raise Unify
       Other effects: None
    *)
    and invertHead (BVar (k), s, _) = BVar (invertVar (k, s))
      | invertHead (H as Const _, s, _) = H
      | invertHead (H as Def _, s, _) = H
      | invertHead (FVar (x, V, s'), s, rOccur) = 
          (invertExp ((V, id), id, rOccur); FVar(x, V, invertSub (s',s)))
	(* invertExp ((V, id), id, rOccur) checks if rOccur appears in V *)
        (* invertSub (s', s) always exists since s' = ^|G| *)

    (* invertSpine ((S, s1), s2, rOccur) = (S[s1])[s2]-1 = S'
       s.t. S'[s2] = S[s1]  and  rOccur not in H, otherwise raises Unify

       Invariant: 
       If   G  |- s1 : G1    G1 |- S : V > W
       and  G  |- s2 : G2    s2 patsub
       and  G  |- (V[s1])[s2]-1  and  G[s2]-1 = G2 exists
       then
       if rOccur does not occur in rigid position in S
       and       G  |- S' : V' > W'
            and  G  |- V [s1] = V' [s2] = V'' : L
            and  G  |- W [s1] = W' [s2] = W'' : L    
            and  G  |- S [s1] = S' [s2] : V'' > W'' 
       then return S' = S[s2]-1
       else raises Unify
       Other effects: instantiation of EVars by lowering or pruning
                      constraints may be added by non-patterns
    *)
    and invertSpine ((Nil, s1), s2, rOccur) = Nil
      | invertSpine ((App (H, S), s1), s2, rOccur) = 
	  App(invertExp ((H, s1), s2, rOccur), 
	      invertSpine ((S, s1), s2, rOccur))
      | invertSpine ((SClo(S, s1'), s1), s2, rOccur) =
	  invertSpine ((S, comp (s1', s1)), s2, rOccur)

    (* invertSub (s1, s2) = s'
       s.t s1 = s' o s2, raises Unify if no such s' exists

       This fixes an oversight in the published version of
       JICSLP'96.  One case of ^n o (k.s2')-1 should be replaced by
       ^n o (k.s2')-1 = (^n o s2'-1) o ^1         if n >= k
       ^n o (k.s2')-1 = (n+1)^(n+1) o (k.s2')-1   if n < k

       Invariant: 
       If   G  |- s1 : G1  and s1 patsub
       and  G  |- s2 : G2  and s2 patsub
       then      G2 |- s' : G1  and s' patsub
            and  s1 = s' o s2
	    and  s' is patsub
       raises Unify is no such s' exists
       Other effects: None
    *)
    and invertSub (Shift (n1), s2 as Shift (n2)) =
        if n1 < n2 
	  then (* this will always fails since n+1 =< n2 *)
	       (* Sat Feb 14 14:50:31 1998 -fp *)
	       (* invertSub (Dot (Idx (n1+1), Shift(n1+1)), s2) *)
	       raise Unify ("Parameter dependency")
	else Shift (n1-n2)
      | invertSub (s1 as Shift (n), s2 as Dot (Idx (k), s2')) =
	(* fixed bug below  Sat Feb 14 14:51:07 1998 -fp *)
	if n >= k
	  then comp (invertSub (s1, s2'), shift)
	else invertSub (Dot (Idx (n+1), Shift (n+1)), s2)
      | invertSub (Dot (Idx (k), s1), s2) =
	  Dot (Idx (invertVar (k, s2)), invertSub (s1, s2))
	  (* front is an index because s1 is a pattern substitution *)

    (* invertDec see invertExp *)
    and invertDec ((Dec (name, V), s1), s2, rOccur) =
          Dec (name, invertExp ((V, s1), s2, rOccur)) 

    (* invertDecP see invertDec *)
    and invertDecP (((D, P), s1), s2, rOccur) =
          (invertDec ((D, s1), s2, rOccur), P) 

    (* unifyExpW ((U1, s1), (U2, s2)) = ()
     
       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf 
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       then if   there is an instantiation I :  
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
	    else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
    and unifyExpW ((Uni (L1), _), (Uni(L2), _)) =
          (* L1 = L2 = type, by invariant *)
          (* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
          ()

      | unifyExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
	  (* s1 = s2 = id by whnf *)
          (* order of calls critical to establish unifySpine invariant *)
          (case (H1, H2) of 
	     (BVar(k1), BVar(k2)) => 
	       if (k1 = k2) then unifySpine ((S1, s1), (S2, s2))
	       else raise Unify "Bound variable clash"
	   | (Const(c1), Const(c2)) => 	  
	       if (c1 = c2) then unifySpine ((S1, s1), (S2, s2))
	       else raise Unify "Constant clash"
	   | (FVar (n1,_,_), FVar (n2,_,_)) =>
	       if (n1 = n2) then unifySpine ((S1, s1), (S2, s2))
	       else raise Unify "Free variable clash"
	   | (Def (d1), Def (d2)) =>
	       if (d1 = d2) then (* because of strict *) 
		 unifySpine ((S1, s1), (S2, s2))
	       else unifyExpW (Whnf.expandDef (Us1), Whnf.expandDef (Us2))
	   | (Def (d1), _) => unifyExpW (Whnf.expandDef Us1, Us2)
	   | (_, Def(d2)) => unifyExpW (Us1, Whnf.expandDef Us2)
	   | _ => raise Unify "Head mismatch")

      | unifyExpW ((Pi (DP1, U1), s1), (Pi (DP2, U2), s2)) =         
	  (unifyDecP ((DP1, s1), (DP2, s2)) ;
	   unifyExp ((U1, dot1 s1), (U2, dot1 s2)) )

      | unifyExpW ((Lam (D1,U1), s1), (Lam (D2,U2), s2)) =           
          (* D1[s1] = D2[s2]  by invariant *)
	  unifyExp ((U1, dot1 s1),(U2, dot1 s2))

      | unifyExpW ((Lam (D1,U1), s1), (U2, s2)) =	                   
	  (* ETA: can't occur if eta expanded *)
	  unifyExp ((U1, dot1 s1), 
		    (Redex (EClo (U2, shift), 
			    App (Root (BVar (1), Nil), Nil)), dot1 s2))
           (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)

      | unifyExpW ((U1, s1), (Lam(D2,U2), s2)) =                     
          (* Cannot occur if expressions are eta expanded *)
	  unifyExp ((Redex (EClo (U1, shift), 
			    App (Root (BVar (1), Nil), Nil)), dot1 s1),
		    (U2, dot1 s2))  
	   (* same reasoning holds as above *)

      | unifyExpW (Us1 as (U1 as EVar(r1, V1, Cnstr1), s1), Us2 as (EVar(r2, V2, Cnstr2),s2)) = 
	  (* postpone, if s1 or s2 are not patsub *)
	  if r1 = r2 then 
	    if Pattern.checkSub(s1) then 
	      if Pattern.checkSub(s2) then
		let val s' = intersection (s1,s2)
		  val V1' = invertExp ((V1, id), s', ref NONE) 
		in
		  instantiateEVarC (r1, EClo (newEVar (V1'), s'), Cnstr1)
		end
	      else Trail.instantiateEVar (r2, newEVarCnstr (V2, Eqn (EClo Us2, EClo Us1)
							        :: Cnstr2))
            else Trail.instantiateEVar (r1, newEVarCnstr (V1, Eqn (EClo Us1, EClo Us2) :: Cnstr1))
	  else
	    if Pattern.checkSub(s1)
	      then instantiateEVarC (r1, invertExpW (Us2, s1, ref NONE), Cnstr1) 
	    else if Pattern.checkSub(s2)
		   then instantiateEVarC (r2, invertExpW (Us1, s2, ref NONE), Cnstr2) 
		 else Trail.instantiateEVar (r1, newEVarCnstr (V1, Eqn (EClo Us1, EClo Us2)
							           :: Cnstr1))

      | unifyExpW (Us1 as (EVar(r, V, Cnstr), s), Us2) =
	if Pattern.checkSub(s)
	  then instantiateEVarC (r, invertExpW (Us2, s, r), Cnstr)
	else 
         Trail.instantiateEVar (r, newEVarCnstr (V, (Eqn (EClo Us1, EClo Us2)) :: Cnstr))

      | unifyExpW (Us1, Us2 as (EVar (r, V, Cnstr), s)) =                       
	if Pattern.checkSub(s) then 
	  instantiateEVarC (r, invertExpW (Us1, s, r), Cnstr) 
	else Trail.instantiateEVar (r, newEVarCnstr (V, (Eqn (EClo Us2, EClo Us1)) :: Cnstr))

      | unifyExpW (Us1,Us2) = 
        raise Unify ("Expression clash")

    (* covers most remaining cases *)
    (* the cases for EClo or Redex should not occur because of whnf invariant *)

    (* unifyExp ((U1, s1), (U2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf 
    *)
    and unifyExp (Us1 as (E1,s1), Us2 as (E2,s2)) = 
          unifyExpW (Whnf.whnf Us1, Whnf.whnf Us2)


    (* unifySpine ((S1, s1), (S2, s2)) = ()
     
       Invariant:
       If   G |- s1 : G1   G1 |- S1 : V1 > W1 
       and  G |- s2 : G2   G2 |- S2 : V2 > W2 
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  G |- W1 [s1] = W2 [s2]  
       then if   there is an instantiation I :
                 s.t. G |- S1 [s1] <I> == S2 [s2] <I> 
            then instantiation is applied as effect, () returned
	    else exception Unify is raised
       Other effects: EVars may be lowered,
                      constraints may be added for non-patterns
    *)
    and unifySpine ((Nil,_), (Nil,_)) = ()
      | unifySpine ((SClo (S1, s1'), s1), Ss) = unifySpine ((S1, comp (s1', s1)), Ss)
      | unifySpine (Ss, (SClo (S2, s2'), s2)) = unifySpine (Ss, (S2, comp (s2', s2)))
      | unifySpine ((App (U1, S1), s1), (App (U2, S2), s2)) = 
          (unifyExp ((U1, s1), (U2, s2)) ; 
	   unifySpine ((S1, s1), (S2, s2)))
      (* Nil/App or App/Nil cannot occur by typing invariants *)

    and unifyDec ((Dec(_, V1), s1), (Dec (_, V2), s2)) =
          unifyExp ((V1, s1), (V2, s2))

    and unifyDecP (((D1, _), s1), ((D2, _), s2)) =
          unifyDec ((D1, s1), (D2, s2))

  in
    val unifyW = unifyExpW
    val unify = unifyExp
    fun unifiable (Us1, Us2) = (unifyExp (Us1, Us2); true) handle Unify _ => false
    val safeInvertExp = safeInvertExp
  end
end;  (* functor Unify *)
