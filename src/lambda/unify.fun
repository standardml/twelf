(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor Unify (structure IntSyn' : INTSYN
	       structure Whnf    : WHNF
	         sharing Whnf.IntSyn = IntSyn'
	       structure Trail   : TRAIL)
  : UNIFY =
struct
  structure IntSyn = IntSyn'
    
  exception Unify of string
  
  local
    open IntSyn

    datatype Action =
      Instantiate of Exp option ref
    | Add of cnstr list ref
    | Solve of cnstr * Cnstr

    datatype CAction = 
      BindCnstr of Cnstr ref * Cnstr

    datatype FAction = 
      BindExp of Exp option ref * Exp option
    | BindAdd of cnstr list ref * CAction list
    | FSolve of Cnstr ref * Cnstr * Cnstr (* ? *)

    type unifTrail = FAction Trail.trail

    val globalTrail = Trail.trail () : Action Trail.trail 


    fun copyCnstr [] = []
      | copyCnstr (refC :: clist) = 
          (BindCnstr (refC, !refC) :: copyCnstr clist)

    fun copy (Instantiate refU) = 
          (BindExp (refU , !refU))
      | copy (Add (cnstrs as ref Cnstrs)) = 
          (BindAdd (cnstrs , copyCnstr(!cnstrs)))
      | copy (Solve (cnstr, Cnstr)) =  
          (FSolve (cnstr, Cnstr, !cnstr)) 


    fun resetCnstr [] = [] 
      | resetCnstr (BindCnstr(refC, Cnstr)::L) = 
          (refC := Cnstr;
	   (refC::(resetCnstr L)))


    fun reset (BindExp (refU, U)) =
          (refU := U;
	   Instantiate refU)
      | reset (BindAdd (cnstrs , CActions)) =
	  (cnstrs := resetCnstr CActions;
	   Add cnstrs)
      | reset (FSolve (refCnstr, Cnstr, Cnstr')) =
	  (refCnstr := Cnstr';
	   Solve (refCnstr, Cnstr))
      

    fun suspend () = Trail.suspend (globalTrail, copy)

    fun resume trail = Trail.resume (trail, globalTrail, reset)
 
    fun undo (Instantiate refU) =
          (refU := NONE)
      | undo (Add (cnstrs as ref(cnstr :: cnstrL))) =
          (cnstrs := cnstrL)
      | undo (Solve (cnstr, Cnstr)) =
          (cnstr := Cnstr)

    fun reset () = Trail.reset globalTrail

    fun mark () = Trail.mark globalTrail

    fun unwind () = Trail.unwind (globalTrail, undo)

    fun addConstraint (cnstrs, cnstr) =
          (
            cnstrs := cnstr :: (!cnstrs);
            Trail.log (globalTrail, Add (cnstrs))
          )

    fun solveConstraint (cnstr as ref (Cnstr)) =
          (
            cnstr := Solved;
            Trail.log (globalTrail, Solve (cnstr, Cnstr))
          )

    (* Associate a constraint to an expression *)
    (* delayExpW ((U, s), cnstr) = ()

       Invariant: 
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then
       the constraint cnstr is added to all the rigid EVar occurrences in U[s]
    *)
    fun delayExpW ((U as Uni(L), s1), _) = ()
      | delayExpW ((Pi ((D, P), U), s), cnstr) = 
          (delayDec ((D, s), cnstr); delayExp ((U, dot1 s), cnstr))
      | delayExpW ((Root (H, S), s), cnstr) =
	  (delayHead (H, cnstr); delaySpine ((S, s), cnstr))
      | delayExpW ((Lam (D, U), s), cnstr) = 
          (delayDec ((D, s), cnstr); delayExp ((U, dot1 s), cnstr))
      | delayExpW ((EVar (G, r, V, cnstrs), s), cnstr) =
          addConstraint(cnstrs, cnstr)
      | delayExpW ((FgnExp (cs, ops), s), cnstr) = (* s = id *)
          delayExp ((#toInternal(ops) (), s), cnstr)
      (* no other cases by invariant *)

    (* delayExp ((U, s), cnstr) = ()
       as in delayExpCW, except that the argument may not be in whnf 
    *)
    and delayExp (Us, cnstr) =
          delayExpW (Whnf.whnf Us, cnstr)

    (* delayHead (H, s, rOccur) = ()

       Invariant: 
       If   G' |- H : V    
       and  G' |- s : G         s is a pattern substitution
       then
       the constraint cnstr is added to a total of n rigid EVar occurrences in H[s]
    *)
    and delayHead (FVar (x, V, s'), cnstr) =
          delayExp ((V, id), cnstr)
      | delayHead (H, _) = ()

    (* delaySpine ((S, s), cnstr) = ()

       Invariant: 
       If   G' |- s : G    G |- S : V > W
       then      G  |- S' : V' > W'
       the constraint cnstr is added to all the rigid EVar occurrences in S[s]
    *)
    and delaySpine ((Nil, s), cnstr) = ()
      | delaySpine ((App (U, S), s), cnstr) =
          (delayExp ((U, s), cnstr); delaySpine ((S, s), cnstr))
      | delaySpine ((SClo(S, s'), s), cnstr) =
	  delaySpine ((S, comp (s', s)), cnstr)

    (* delayDec see delayExp *)
    and delayDec ((Dec (name, V), s), cnstr) =
          delayExp ((V, s), cnstr)

    local
      val awakenCnstrs = ref nil : cnstr list ref
    in
      fun resetAwakenCnstrs () = (awakenCnstrs := nil)

      fun nextCnstr () = 
            case !awakenCnstrs
              of nil => NONE
               | (cnstr :: cnstrL) => 
                   (awakenCnstrs := cnstrL; SOME(cnstr))

      (* Instantiating EVars  *)
      fun instantiateEVar (refU, V, cnstrL) =
            (
              refU := SOME(V);
              Trail.log (globalTrail, Instantiate (refU));
              awakenCnstrs := cnstrL @ !awakenCnstrs
            )

      fun postponeUnify (G, U1, U2) =
            awakenCnstrs := ref (Eqn (G, U1, U2)) :: !awakenCnstrs
    end  (* local *)

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


    (* weakenSub (G1, s, ss) = w'
     
       Invariant:
       If    G |- s : G1       (* s patsub *)
       and   G2 |- ss : G      (* ss strsub *)
       then  G1 |- w' : G1'    (* w' weaksub *)
    *)

    fun weakenSub (G, Shift n, ss) =
        if n < ctxLength G 
	  then weakenSub (G, Dot (Idx (n+1), Shift (n+1)), ss)
	else id
      | weakenSub (G, Dot (Idx n, s'), ss) =
        (case bvarSub (n, ss)
 	   of Undef => comp (weakenSub (G, s', ss), shift)
	    | Idx _ => dot1 (weakenSub (G, s', ss)))
	    (* no other cases, ss is strsub *)
      | weakenSub (G, Dot (Undef, s'), ss) =
	   comp (weakenSub (G, s', ss), shift)

    (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       G |- U : V    G' |- s : G  (G' |- U[s] : V[s])
       G'' |- ss : G'

       Effect: prunes EVars in U[s] according to ss
               raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
    fun pruneExp  (G, Us, ss, rOccur, prunable) = pruneExpW (G, Whnf.whnf Us, ss, rOccur, prunable)
    and pruneExpW (G, (U as Uni _, s), _, _, _) = U
      | pruneExpW (G, (Pi ((D, P), V), s), ss, rOccur, prunable) = 
          Pi ((pruneDec (G, (D, s), ss, rOccur, prunable), P),
	      pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur, prunable))
      | pruneExpW (G, (Lam (D, V), s), ss, rOccur, prunable) =
	  Lam (pruneDec (G, (D, s), ss, rOccur, prunable),
	       pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur, prunable))
      | pruneExpW (G, (Root (H, S), s (* = id *)), ss, rOccur, prunable) = 
	  Root (pruneHead (G, H, ss, rOccur, prunable),
		pruneSpine (G, (S, s), ss, rOccur, prunable))
      | pruneExpW (G, (X as EVar (r, GX, V, cnstrs), s), ss, rOccur, prunable) = 
	  if (rOccur = r) then raise Unify "Variable occurrence"
	  else if Whnf.isPatSub (s) then
	       let
		 val w = weakenSub (G, s, ss)
	       in
		 if Whnf.isId w
		   then EClo (X, comp (s, ss))
		 else if prunable then
		   let
		     val wi = Whnf.invert w
                     (* val V' = EClo (V, wi) *)
		     val V' = pruneExp (GX, (V, id), wi, rOccur, prunable)
                     (* val GY = Whnf.strengthen (wi, GX) *)
		     val GY = pruneCtx (wi, GX, rOccur, prunable)
		     (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
		     (* could optimize by checking for identity subst *)
		     val Y = newEVar (GY, V')
		     val Yw = EClo (Y, w)
		     val _ = instantiateEVar (r, Yw, !cnstrs)
		   in
		     EClo (Yw, comp (s, ss))
		   end
		      else raise Unify "Not prunable"
	       end
	       else (* s not patsub *)
                 (
		   EClo (X, pruneSub (G, s, ss, rOccur, false))
		   handle Unify (msg) => 
		     if prunable then
		       let 
		         (* val GY = Whnf.strengthen (ss, G) *)
                         (* shortcuts possible by invariants on G? *)
                         val GY = pruneCtx (ss, G, rOccur, prunable)
                         (* val V' = EClo (V, comp (s, ss)) *)
		         val V' = pruneExp (G, (V, s), ss, rOccur, prunable)
		         val Y = newEVar (GY, V')
                         (* add another constraint if at type level? -kw *)
		         val _ = addConstraint (cnstrs, ref (Eqn (G, EClo (X, s),
							             EClo (Y, Whnf.invert ss))))
		       in
		         Y
		       end
		     else raise Unify (msg)
                 )
      | pruneExpW (G, (FgnExp (_, ops), s), ss, rOccur, prunable) =
          #map(ops) (fn U => pruneExp (G, (U, s), ss, rOccur, prunable))
      (* other cases impossible since (U,s1) whnf *)
    and pruneDec (G, (Dec (name, V), s), ss, rOccur, prunable) =
	  Dec (name, pruneExp (G, (V, s), ss, rOccur, prunable))
    and pruneSpine (G, (Nil, s), ss, rOccur, prunable) = Nil
      | pruneSpine (G, (App (U, S), s), ss, rOccur, prunable) = 
	  App (pruneExp (G, (U, s), ss, rOccur, prunable),
	       pruneSpine (G, (S, s), ss, rOccur, prunable))
      | pruneSpine (G, (SClo (S, s'), s), ss, rOccur, prunable) = 
	  pruneSpine (G, (S, comp (s', s)), ss, rOccur, prunable)
    and pruneHead (G, BVar k, ss, rOccur, prunable) = 
        (case (bvarSub (k, ss))
	   of Undef => raise Unify "Parameter dependency"
	    | Idx k' => BVar k')
      | pruneHead (G, H as Const _, ss, rOccur, prunable) = H
      | pruneHead (G, Proj (LVar (r, l, s), i), ss, rOccur, prunable) = 
	   Proj (LVar (r, l, pruneSub (G, s, ss, rOccur, prunable)), i)
      | pruneHead (G, H as Skonst _, ss, rOccur, prunable) = H
      | pruneHead (G, H as Def _, ss, rOccur, prunable) = H
      | pruneHead (G, FVar (x, V, s'), ss, rOccur, prunable) =
	  (* V does not to be pruned, since . |- V : type and s' = ^k *)
	  (* perform occurs-check for r only *)
	  (pruneExp (G, (V, id), id, rOccur, prunable);
	   FVar (x, V, comp (s', ss)))
      | pruneHead (G, H as FgnConst _, ss, rOccur, prunable) = H
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant 
       doesn't hold any more, because substitutions do not
       only occur in EVar's any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    and pruneSub (G, s as Shift (n), ss, rOccur, prunable) =
        if n < ctxLength (G) 
	  then pruneSub (G, Dot (Idx (n+1), Shift (n+1)), ss, rOccur, prunable)
	else comp (s, ss)		(* must be defined *)
      | pruneSub (G, Dot (Idx (n), s'), ss, rOccur, prunable) =
	(case bvarSub (n, ss)
	   of Undef => raise Unify "Not prunable"
	    | Ft => Dot (Ft, pruneSub (G, s', ss, rOccur, prunable)))
      | pruneSub (G, Dot (Exp (U), s'), ss, rOccur, prunable) =
	  (* below my raise Unify *)
	  Dot (Exp (pruneExp (G, (U, id), ss, rOccur, prunable)),
	       pruneSub (G, s', ss, rOccur, prunable))
      (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* Pruning establishes and maintains this invariant *)
    and pruneCtx (Shift n, Null, rOccur, prunable) = Null
      | pruneCtx (Dot (Idx k, t), Decl (G, D), rOccur, prunable) =
        let 
	  val t' = comp (t, invShift)
	  val D' = pruneDec (G, (D, id), t', rOccur, prunable)
	in
          Decl (pruneCtx (t', G, rOccur, prunable), D')
	end
      | pruneCtx (Dot (Undef, t), Decl (G, d), rOccur, prunable) = 
          pruneCtx (t, G, rOccur, prunable)
      | pruneCtx (Shift n, G, rOccur, prunable) = 
	  pruneCtx (Dot (Idx (n+1), Shift (n+1)), G, rOccur, prunable)

    fun isUniType (V, s) =
        (case Whnf.whnf (V, s)
           of (Uni Type, _) => true
            | _ => false)

    (* copyTypeW (G, (G1, s1), (V, s2)) = V'
       If   G |~ s1 : G1
            G |~ s2 : G2   G2 |~ V : L   (V,s2) in whnf
       then G1 |~ V' : type
        and G  |~ V [s2] <I> ~~ V' [s1] <I> : type
        and instantiation I is applied
    *)
    fun copyTypeW (G, (G1, s1), (V as Uni _, s2)) = V
      | copyTypeW (G, (G1, s1), (Pi ((D as Dec (name, V1), P), V2), s2)) =
        let
          val V1' = copyType (G, (G1, s1), (V1, s2))
          val D' = Dec (name, V1')
          val V2' = copyType (Decl (G, decSub (D, s2)),
                              (Decl (G1, D'), dot1 s1), (V2, dot1 s2))
        in
          Pi ((D', P), V2')
        end
      | copyTypeW (G, (G1, s1), (Root (H as Const (c), S), s2)) =
        let
          val V = constType (c)
        in
          Root (H, copySpine (G, (G1, s1, (V, id)), (S, s2)))
        end
      | copyTypeW (G, (G1, s1), Vs2 as (EVar _, s2)) =
        let
          val X = newTypeVar (G1)
        in
          postponeUnify (G, EClo (X, s1), EClo Vs2);
          X
        end

    and copyType (G, (G1, s1), Vs2) =
          copyTypeW (G, (G1, s1), Whnf.whnf Vs2)

    (* copySpine (G, (G1, s1, (V, s2)), (S, s3)) = S'
        pre: G  |- s1 : G1
             G1 |- s2 : G2  G2 |- V : L
             G  |- s3 : G3  G3 |- S : Vs > a
             G  |- Vs[s3] = V[s2][s1]
       post: G1 |- S' : V[s2] > a'
             G  |- a[s3] = a'[s1]
             G  |- S[s3] = S'[s1]
     *)
       
    and copySpine (G, (G1, s1, (V, s2)), (Nil, s3)) = Nil
      | copySpine (G, (G1, s1, (Pi ((Dec (_, V1), _), V2), s2)), (App (U, S), s3)) =
        let
          (* FIX: should be newLoweredEVar -kw *)
          val U' = newEVar (G1, EClo (V1, s2))
        in
          postponeUnify (G, EClo (U', s1), EClo (U, s3));
          App (U', copySpine (G, (G1, s1, (V2, Whnf.dotEta (Exp (U'), s2))), (S, s3)))
        end
      | copySpine (G, (G1, s1, (V, s2)), (SClo (S, s), s3)) =
          copySpine (G, (G1, s1, (V, s2)), (S, comp (s, s3)))

    (* unifyExpW (G, (U1, s1), (U2, s2)) = ()
     
       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf 
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :  
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
	    else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
    and unifyExpW (G, Us1 as (FgnExp (_, ops), _), Us2) =
          (case (#unifyWith(ops) (G, EClo Us2))
             of (Succeed residualL) =>
                  let
                    fun execResidual (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                          let
                            val W' = pruneExp (G, (W, id), ss, r, true)
                          in
                            instantiateEVar (r, W', !cnstrs)
                          end
                      | execResidual (Delay (U, cnstr)) =
                          delayExp ((U, id), cnstr)
                  in
                    List.app execResidual residualL
                  end
              | Fail => raise Unify "Foreign Expression Mismatch")

      | unifyExpW (G, Us1, Us2 as (FgnExp (_, ops), _)) =
          (case (#unifyWith(ops) (G, EClo Us1))
             of (Succeed opL) =>
                  let
                    fun execOp (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                          let
                            val W' = pruneExp (G, (W, id), ss, r, true)
                          in
                            instantiateEVar (r, W', !cnstrs)
                          end
                      | execOp (Delay (U, cnstr)) = delayExp ((U, id), cnstr)
                  in
                    List.app execOp opL
                  end
              | Fail => raise Unify "Foreign Expression Mismatch")

      | unifyExpW (G, (Uni (L1), _), (Uni(L2), _)) =
          (* L1 = L2 = type, by invariant *)
          (* unifyUni (L1, L2) - removed Mon Aug 24 12:18:24 1998 -fp *)
          ()

      | unifyExpW (G, Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
	  (* s1 = s2 = id by whnf *)
          (* order of calls critical to establish unifySpine invariant *)
          (case (H1, H2) of 
	     (BVar(k1), BVar(k2)) => 
	       if (k1 = k2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Bound variable clash"
	   | (Const(c1), Const(c2)) => 	  
	       if (c1 = c2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Constant clash"
	   | (Proj (b1, i1), Proj (b2, i2)) =>
		 if i1 <> i2 then raise Unify "Global parameter clash"
		 else 
		   (case (b1, b2)
		     of (LVar (r1, l1, t1), L as LVar (r2, l2, t2)) =>
			  if l1 <> l2 then
			    raise Unify "Label clash"
			  else
			    (* S(l) = Gsome, Lblock
			       G1 |- s1 : Gsome 
			       G2 |- s2 : Gsome *)
			    (* (unifySub (G, comp (t1, s1), comp (t2, s2)); *)
			    (unifySub (G, comp (t1, s1), comp (t2, s2));
			     unifySub (G, t1, t2);
			    r1 := SOME L))
	   | (Skonst(c1), Skonst(c2)) => 	  
	       if (c1 = c2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Skolem constant clash"
	   | (FVar (n1,_,_), FVar (n2,_,_)) =>
	       if (n1 = n2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Free variable clash"
	   | (Def (d1), Def (d2)) =>
	       if (d1 = d2) then (* because of strict *) 
		 unifySpine (G, (S1, s1), (S2, s2))
	       else unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2))
	   | (Def (d1), _) => unifyExpW (G, Whnf.expandDef Us1, Us2)
	   | (_, Def(d2)) => unifyExpW (G, Us1, Whnf.expandDef Us2)
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst (cs2, ConDec (n2, _, _, _, _, _))) =>
               (* we require unique string representation of external constants *)
               if (cs1 = cs2) andalso (n1 = n2) then ()
               else raise Unify "Foreign Constant clash"
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _)), FgnConst (cs2, ConDef (n2, _, _, V, W2, _))) =>
               if (cs1 = cs2) andalso (n1 = n2) then ()
               else unifyExp (G, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _)), _) =>
               unifyExp (G, (W1, s1), Us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _))) =>
               unifyExp (G, Us1, (W2, s2))              
	   | _ => raise Unify "Head mismatch")

      | unifyExpW (G, (Pi ((D1, _), U1), s1), (Pi ((D2, _), U2), s2)) =         
	  (unifyDec (G, (D1, s1), (D2, s2)) ;
	   unifyExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), (U2, dot1 s2)))

      | unifyExpW (G, (Lam (D1, U1), s1), (Lam (D2, U2), s2)) =           
          (* D1[s1] = D2[s2]  by invariant *)
	  unifyExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1),(U2, dot1 s2))

      | unifyExpW (G, (Lam (D1, U1), s1), (U2, s2)) =	                   
	  (* ETA: can't occur if eta expanded *)
	  unifyExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), 
		    (Redex (EClo (U2, shift), App (Root (BVar (1), Nil), Nil)), dot1 s2))
           (* for rhs:  (U2[s2])[^] 1 = U2 [s2 o ^] 1 = U2 [^ o (1. s2 o ^)] 1
                        = (U2 [^] 1) [1.s2 o ^] *)

      | unifyExpW (G, (U1, s1), (Lam (D2, U2), s2)) =                     
          (* Cannot occur if expressions are eta expanded *)
	  unifyExp (Decl (G, decSub (D2, s2)), 
		    (Redex (EClo (U1, shift), App (Root (BVar (1), Nil), Nil)), dot1 s1),
		    (U2, dot1 s2))  
	   (* same reasoning holds as above *)

      | unifyExpW (G, Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
		   Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
	  (* postpone, if s1 or s2 are not patsub *)
	  if r1 = r2 then 
	    if Whnf.isPatSub(s1) then 
	      if Whnf.isPatSub(s2) then
		let
		  val s' = intersection (s1,s2)	(* compute s' directly? *)
		  val ss' = Whnf.invert s'
		  val V1' = EClo (V1, ss')  (* invertExp ((V1, id), s', ref NONE) *)
		  val G1' = Whnf.strengthen (ss', G1)
		in
		  instantiateEVar (r1, EClo (newEVar (G1', V1'), s'), !cnstrs1)
		end
	      else addConstraint (cnstrs2, ref (Eqn (G, EClo Us2, EClo Us1)))
            else addConstraint (cnstrs1, ref (Eqn (G, EClo Us1, EClo Us2)))
	  else
	    if Whnf.isPatSub(s1) then 
	      let
		val ss1 = Whnf.invert s1
		val U2' = pruneExp (G, Us2, ss1, r1, true)   (* prunable set to true -cs *)
	      in
		(* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
		(* invertExpW (Us2, s1, ref NONE) *)
		instantiateEVar (r1, U2', !cnstrs1)
	      end
	    else if Whnf.isPatSub(s2) then 
	      let
		val ss2 = Whnf.invert s2
		val U1' = pruneExp (G, Us1, ss2, r2, true)
	      in
		(* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
	        (* invertExpW (Us1, s2, ref NONE) *)
		instantiateEVar (r2, U1', !cnstrs2)
	      end
            else
              let
                val cnstr = ref (Eqn (G, EClo Us1, EClo Us2))
              in
                addConstraint (cnstrs1, cnstr);
                if isUniType (V1, s1)
                  then addConstraint (cnstrs2, cnstr)
                else ()
              end

      | unifyExpW (G, Us1 as (EVar(r, GX, V, cnstrs), s), Us2 as (U2,s2)) =
	if Whnf.isPatSub(s) then
	  let val ss = Whnf.invert s
	      val U2' = pruneExp (G, Us2, ss, r, true) (* could raise occurs-check *)
	  in
	    (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
	    (* invertExpW (Us2, s, r) *)
	    instantiateEVar (r, U2', !cnstrs)
	  end
	else if isUniType (V, s) then
          instantiateEVar (r, copyType (G, (GX, s), Us2), !cnstrs)
        else
          addConstraint (cnstrs, ref (Eqn (G, EClo Us1, EClo Us2)))

      | unifyExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
	if Whnf.isPatSub(s) then 
	  let val ss = Whnf.invert s
	      val U1' = pruneExp (G, Us1, ss, r, true)
	  in
	    (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
	    (* invertExpW (Us1, s, r) *)
	    instantiateEVar (r, U1', !cnstrs)
	  end
        else if isUniType (V, s) then
          instantiateEVar (r, copyType (G, (GX, s), Us1), !cnstrs)
        else
          addConstraint (cnstrs, ref (Eqn (G, EClo Us1, EClo Us2)))

      | unifyExpW (G, Us1, Us2) = 
        raise Unify ("Expression clash")

    (* covers most remaining cases *)
    (* the cases for EClo or Redex should not occur because of whnf invariant *)

    (* unifyExp (G, (U1, s1), (U2, s2)) = ()
       as in unifyExpW, except that arguments may not be in whnf 
    *)
    and unifyExp (G, Us1 as (E1,s1), Us2 as (E2,s2)) = 
          unifyExpW (G, Whnf.whnf Us1, Whnf.whnf Us2)

    (* unifySpine (G, (S1, s1), (S2, s2)) = ()
     
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
    and unifySpine (G, (Nil,_), (Nil,_)) = ()
      | unifySpine (G, (SClo (S1, s1'), s1), Ss) = unifySpine (G, (S1, comp (s1', s1)), Ss)
      | unifySpine (G, Ss, (SClo (S2, s2'), s2)) = unifySpine (G, Ss, (S2, comp (s2', s2)))
      | unifySpine (G, (App (U1, S1), s1), (App (U2, S2), s2)) = 
          (unifyExp (G, (U1, s1), (U2, s2)) ; 
	   unifySpine (G, (S1, s1), (S2, s2)))
      (* Nil/App or App/Nil cannot occur by typing invariants *)

    and unifyDec (G, (Dec(_, V1), s1), (Dec (_, V2), s2)) =
          unifyExp (G, (V1, s1), (V2, s2))

    (* unifySub (G, s1, s2) = ()
     
       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then unifySub (G, s1, s2) terminates with () 
	    iff there exists an instantiation I, such that
	    s1 [I] = s2 [I]

       Remark:  unifySub is used only to unify the instantiation of SOME variables
    *)
	 
    and unifySub (G, Shift (n1), Shift (n2)) = ()
         (* by invariant *)
      | unifySub (G, Shift(n), s2 as Dot _) = 
          unifySub (G, Dot(Idx(n+1), Shift(n+1)), s2)
      | unifySub (G, s1 as Dot _, Shift(m)) = 
	  unifySub (G, s1, Dot(Idx(m+1), Shift(m+1)))
      | unifySub (G, Dot(Ft1,s1), Dot(Ft2,s2)) =
	  ((case (Ft1, Ft2) of
	     (Idx (n1), Idx (n2)) => 
	       if n1 <> n2 then raise Error "SOME variables mismatch"
	       else ()                      
           | (Exp (U1), Exp (U2)) => unifyExp (G, (U1, id), (U2, id))
	   | (Exp (U1), Idx (n2)) => unifyExp (G, (U1, id), (Root (BVar (n2), Nil), id))
           | (Idx (n1), Exp (U2)) => unifyExp (G, (Root (BVar (n1), Nil), id), (U2, id)));
(*	   | (Undef, Undef) => 
	   | _ => false *)   (* not possible because of invariant? -cs *)
	  unifySub (G, s1, s2))


    fun unify1W (G, Us1, Us2) =
          (unifyExpW (G, Us1, Us2); awakeCnstr (nextCnstr ()))

    and unify1 (G, Us1, Us2) =
          (unifyExp (G, Us1, Us2); awakeCnstr (nextCnstr ()))

    and awakeCnstr (NONE) = ()
      | awakeCnstr (SOME(ref Solved)) = awakeCnstr (nextCnstr ())
      | awakeCnstr (SOME(cnstr as ref (Eqn (G, U1, U2)))) =
          (solveConstraint cnstr;
           unify1 (G, (U1, id), (U2, id)))
      | awakeCnstr (SOME(ref (FgnCnstr (cs, ops)))) =
          if (#awake(ops)()) then ()
          else raise Unify "Foreign constraint violated"

    fun unifyW (G, Us1, Us2) =
          (resetAwakenCnstrs (); unify1W (G, Us1, Us2))

    fun unify (G, Us1, Us2) =
          (resetAwakenCnstrs (); unify1 (G, Us1, Us2))


    (* Shape unification
       V1 ~~ V2 means that two types have the same shape
       G |~ ... means that an object is well-typed up to shape
    *)

    (* shapeExpW (G, (U1, s1), (U2, s2)) = ()

       Invariant:
       If   G |~ s1 : G1   G1 |~ U1 : L  (U1,s1) in whnf
       and  G |~ s2 : G2   G2 |~ U2 : L  (U2,s2) in whnf 
       then if   there is an instantiation I :  
                 s.t. G |~ U1 [s1] <I> ~~ U2 [s2] <I>
            then instantiation is applied as effect, () returned
            else exception Unify is raised
       Other effects: constraints may be added for flex-flex equations
    *)
    (* FIX: need FgnExp case *)
    fun shapeExpW (Root (H1, _ (* Nil *)), Root (H2, _ (* Nil *))) =
          (case (H1, H2) of
             (Const(c1), Const(c2)) =>
               if (c1 = c2) then ()
               else raise Unify "Constant clash"
             (* FIX: need FgnConst case *)
             (* all other cases impossible by invariant *))

      | shapeExpW (Uni Type, Uni Type) = ()

      | shapeExpW (Pi ((Da1, _), Va1), Pi ((Da2, _), Va2)) =
          (shapeDec (Da1, Da2);
           shapeExp (Va1, Va2))

      | shapeExpW (Va1 as EVar(r1, G1, V1, _ (* ref nil *)),
                   Va2 as EVar(r2, G2, V2, _ (* ref nil *))) =
        if r1 = r2
          then ()
        else
          instantiateEVar (r1, Va2, nil)
      | shapeExpW (EVar (r, GX, L, _ (* ref nil *)), Va2) =
          (shapeOccurExpW (r, Va2); instantiateEVar (r, Va2, nil))
      | shapeExpW (Va1, EVar (r, GX, V, _ (* ref nil *))) =
          (shapeOccurExpW (r, Va1); instantiateEVar (r, Va1, nil))

      | shapeExpW (Va1, Va2) =
          raise Unify ("Shape clash")

    and shapeExp (Va1, Va2) =
        let
          val (Va1', _) = Whnf.whnf (Va1, IntSyn.id)
          val (Va2', _) = Whnf.whnf (Va2, IntSyn.id)
        in
          shapeExpW (Va1', Va2')
        end

    and shapeDec (Dec(_, Va1), Dec (_, Va2)) =
          shapeExp (Va1, Va2)

    and shapeOccurExpW (r, Pi ((Da1, _), Va1)) =
          (shapeOccurDec (r, Da1); shapeOccurExp (r, Va1))
      | shapeOccurExpW (r, EVar (r1, _, _, _)) =
          if r = r1 then raise Unify ("Variable occurence")
          else ()
      | shapeOccurExpW (r, _) = ()

    and shapeOccurExp (r, Va1) =
        let
          val (Va1', _) = Whnf.whnf (Va1, IntSyn.id)
        in
          shapeOccurExpW (r, Va1')
        end

    and shapeOccurDec (r, Dec (_, Va1)) = shapeOccurExp (r, Va1)

    fun shape (Va1, Va2) = shapeExp (Va1, Va2)

  in
    type unifTrail = unifTrail

    val reset = reset
    val mark = mark
    val unwind = unwind

    val suspend = suspend
    val resume = resume

    val delay = delayExp

    val instantiateEVar = instantiateEVar
    val addConstraint = addConstraint
    val solveConstraint = solveConstraint

    val intersection = intersection

    val unifyW = unifyW     
    val unify = unify
    val shape = shape

    fun invertible (G, Us, ss, rOccurr) =
          (pruneExp (G, Us, ss, rOccurr, false); true)
          handle Unify _ => false

    fun unifiable (G, Us1, Us2) =
          (unify (G, Us1, Us2); true)
          handle Unify _ => false

    fun unifiable' (G, Us1, Us2) = 
          (unify (G, Us1, Us2); NONE)
          handle Unify(msg) => SOME(msg)
  end
end;  (* functor Unify *)
