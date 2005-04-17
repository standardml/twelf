(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor Unify ((*! structure IntSyn' : INTSYN !*)
	       structure Whnf    : WHNF
	       (*! sharing Whnf.IntSyn = IntSyn' !*)
	       structure Trail   : TRAIL)
  : UNIFY =
struct
  (*! structure IntSyn = IntSyn' !*)
    
  exception Unify of string
  exception NotInvertible
  
  local
    open IntSyn

    datatype Action =
      Instantiate of Exp option ref
    | InstantiateBlock of Block option ref
    | Add of cnstr list ref
    | Solve of cnstr * Cnstr

    datatype CAction = 
      BindCnstr of Cnstr ref * Cnstr

    datatype FAction = 
      BindExp of Exp option ref * Exp option
    | BindBlock of Block option ref * Block option
    | BindAdd of cnstr list ref * CAction list
    | FSolve of Cnstr ref * Cnstr * Cnstr (* ? *)

    type unifTrail = FAction Trail.trail

    val globalTrail = Trail.trail () : Action Trail.trail 

 fun frontToString (Idx i) = "(idx " ^ Int.toString i ^ ")"
      | frontToString (Exp E) = " exp _ "
      | frontToString (Undef) = " undef "

    fun subToString (Shift i) = "(shift " ^ Int.toString i ^ ")"
      | subToString (Dot(ft, s)) = frontToString ft ^ ". " ^ subToString s


    fun copyCnstr [] = []
      | copyCnstr (refC :: clist) = 
          (BindCnstr (refC, !refC) :: copyCnstr clist)

    fun copy (Instantiate refU) = 
          (BindExp (refU , !refU))
      | copy (InstantiateBlock refB) = 
          (BindBlock (refB , !refB))
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
      | reset (BindBlock (refB, B)) =
          (refB := B;
	   InstantiateBlock refB)
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
      | undo (InstantiateBlock refB) =
	  (refB := NONE)
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
      | delayExpW ((FgnExp csfe, s), cnstr) = (* s = id *)
          FgnExpStd.App.apply csfe (fn U => delayExp ((U, s), cnstr))
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

      (* Instantiating LVars  *)
      fun instantiateLVar (refB, B) =
            (
              refB := SOME(B);
              Trail.log (globalTrail, InstantiateBlock (refB))
            )
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

       and   G2 |- w' o s o ss : G1'  is fully defined
       and   G1' is maximal such
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

    (* invert (G, (U, s), ss, rOccur) = U[s][ss]

       G |- s : G'   G' |- U : V  (G |- U[s] : V[s])
       G'' |- ss : G

       Effect: raises NotInvertible if U[s][ss] does not exist
               or rOccurs occurs in U[s]
               does NOT prune EVars in U[s] according to ss; fails instead
    *)
    fun invertExp (G, Us, ss, rOccur) =
          invertExpW (G, Whnf.whnf Us, ss, rOccur)
    and invertExpW (G, (U as Uni _, s), _, _) = U
      | invertExpW (G, (Pi ((D, P), V), s), ss, rOccur) = 
          Pi ((invertDec (G, (D, s), ss, rOccur), P),
	      invertExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur))
      | invertExpW (G, (Lam (D, V), s), ss, rOccur) =
	  Lam (invertDec (G, (D, s), ss, rOccur),
	       invertExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur))
      | invertExpW (G, (Root (H, S), s (* = id *)), ss, rOccur) = 
	  Root (invertHead (G, H, ss, rOccur),
		invertSpine (G, (S, s), ss, rOccur))
      | invertExpW (G, (X as EVar (r, GX, V, cnstrs), s), ss, rOccur) = 
	  if (rOccur = r) then raise NotInvertible
	  else if Whnf.isPatSub (s) then
	       let
		 val w = weakenSub (G, s, ss)
	       in
		 if Whnf.isId w
		   then EClo (X, comp (s, ss))
		 else raise NotInvertible
	       end
	       else (* s not patsub *)
		 (* invertExp may raise NotInvertible *)
		 EClo (X, invertSub (G, s, ss, rOccur))
      | invertExpW (G, (FgnExp csfe, s), ss, rOccur) =
          FgnExpStd.Map.apply csfe (fn U => invertExp (G, (U, s), ss, rOccur))

      (* other cases impossible since (U,s1) whnf *)
    and invertDec (G, (Dec (name, V), s), ss, rOccur) =
	  Dec (name, invertExp (G, (V, s), ss, rOccur))
    and invertSpine (G, (Nil, s), ss, rOccur) = Nil
      | invertSpine (G, (App (U, S), s), ss, rOccur) = 
	  App (invertExp (G, (U, s), ss, rOccur),
	       invertSpine (G, (S, s), ss, rOccur))
      | invertSpine (G, (SClo (S, s'), s), ss, rOccur) = 
	  invertSpine (G, (S, comp (s', s)), ss, rOccur)
    and invertHead (G, BVar k, ss, rOccur) = 
        (case (bvarSub (k, ss))
	   of Undef => raise NotInvertible
	    | Idx k' => BVar k')
      | invertHead (G, H as Const _, ss, rOccur) = H
      | invertHead (G, Proj (B as Bidx k, i), ss, rOccur) =
	(* blockSub (B, ss) should always be defined *)
	(* Fri Dec 28 10:03:12 2001 -fp !!! *)
	(case blockSub (B, ss)
	   of Bidx(k') => Proj (Bidx (k'), i))
      | invertHead (G, H as Proj (LVar (r, sk, (l, t)), i), ss, rOccur) = 
        (* claim: LVar does not need to be pruned since . |- t : Gsome *)
	(* so we perform only the occurs-check here as for FVars *)
	(* Sat Dec  8 13:39:41 2001 -fp !!! *)
	(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
	(* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
	   ( invertSub (G, t, id, rOccur) ;
	     H )
      | invertHead (G, H as Skonst _, ss, rOccur) = H
      | invertHead (G, H as Def _, ss, rOccur) = H
      | invertHead (G, FVar (x, V, s'), ss, rOccur) =
	  (* V does not to be pruned, since . |- V : type and s' = ^k *)
	  (* perform occurs-check for r only *)
	  (invertExp (G, (V, id), id, rOccur);  (* why G here? -fp !!! *)
	   FVar (x, V, comp (s', ss)))
      | invertHead (G, H as FgnConst _, ss, rOccur) = H
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant 
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    and invertSub (G, s as Shift (n), ss, rOccur) =
        if n < ctxLength (G) 
	  then invertSub (G, Dot (Idx (n+1), Shift (n+1)), ss, rOccur)
	else comp (s, ss)		(* must be defined *)
      | invertSub (G, Dot (Idx (n), s'), ss, rOccur) =
	(case bvarSub (n, ss)
	   of Undef => raise NotInvertible
	    | Ft => Dot (Ft, invertSub (G, s', ss, rOccur)))
      | invertSub (G, Dot (Exp (U), s'), ss, rOccur) =
	  (* below my raise NotInvertible *)
	  Dot (Exp (invertExp (G, (U, id), ss, rOccur)),
	       invertSub (G, s', ss, rOccur))
      (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* Pruning establishes and maintains this invariant *)
    (* invertCtx does not appear to be necessary *)
    (*
    and invertCtx (Shift n, Null, rOccur) = Null
      | invertCtx (Dot (Idx k, t), Decl (G, D), rOccur) =
        let 
	  val t' = comp (t, invShift)
	  val D' = invertDec (G, (D, id), t', rOccur)
	in
          Decl (invertCtx (t', G, rOccur), D')
	end
      | invertCtx (Dot (Undef, t), Decl (G, d), rOccur) = 
          invertCtx (t, G, rOccur)
      | invertCtx (Shift n, G, rOccur) = 
	  invertCtx (Dot (Idx (n+1), Shift (n+1)), G, rOccur)
    *)

    (* prune (G, (U, s), ss, rOccur) = U[s][ss]

       G |- s : G'   G' |- U : V  (G  |- U[s] : V[s])
       G'' |- ss : G

       Effect: prunes EVars in U[s] according to ss
               raises Unify if U[s][ss] does not exist, or rOccur occurs in U[s]
    *)
    fun pruneExp  (G, Us, ss, rOccur) = 
          pruneExpW (G, Whnf.whnf Us, ss, rOccur)
    and pruneExpW (G, (U as Uni _, s), _, _) = U
      | pruneExpW (G, (Pi ((D, P), V), s), ss, rOccur) = 
          Pi ((pruneDec (G, (D, s), ss, rOccur), P),
	      pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur))
      | pruneExpW (G, (Lam (D, V), s), ss, rOccur) =
	  Lam (pruneDec (G, (D, s), ss, rOccur),
	       pruneExp (Decl (G, decSub (D, s)), (V, dot1 s), dot1 ss, rOccur))
      | pruneExpW (G, (Root (H, S), s (* = id *)), ss, rOccur) = 
	  Root (pruneHead (G, H, ss, rOccur),
		pruneSpine (G, (S, s), ss, rOccur))
      | pruneExpW (G, (X as EVar (r, GX, V, cnstrs), s), ss, rOccur) = 
	  if (rOccur = r) then raise Unify "Variable occurrence"
	  else if Whnf.isPatSub (s) then
	       let
		 val w = weakenSub (G, s, ss)
	       in
		 if Whnf.isId w
		   then EClo (X, comp (s, ss))
		 else
		   let
		     val wi = Whnf.invert w
                     (* val V' = EClo (V, wi) *)
		     val V' = pruneExp (GX, (V, id), wi, rOccur)
                     (* val GY = Whnf.strengthen (wi, GX) *)
		     val _ = print "ADAM333"


    fun subToString' (Shift k) = "Shift " ^ (Int.toString k)
      | subToString' (Dot (Idx k, t)) = "Idx " ^ (Int.toString k) ^ " . " ^ subToString'(t)
      | subToString' (Dot (Block _, t)) = "Block" ^ " . " ^ subToString'(t)
      | subToString' (Dot (Exp _, t)) = "Exp" ^ " . " ^ subToString'(t)
      | subToString' (Dot (Undef, t)) = "Undef" ^ " . " ^ subToString'(t)


		     val _ = print (subToString' s) 
		     val _ = print "\n\n" 
		     val _ = print (subToString' ss) 
		     val _ = print "\n\n" 
		     val _ = print (subToString' w) 
		     val _ = print "\n\n" 


		     val _ = print (Int.toString(ctxLength(GX)))
		     val GY = pruneCtx (wi, GX, rOccur)
		     val _ = print "ADAM444"
		     (* shortcut on GY possible by invariant on GX and V[s]? -fp *)
		     (* could optimize by checking for identity subst *)
		     val Y = newEVar (GY, V')
		     val Yw = EClo (Y, w)
		     val _ = instantiateEVar (r, Yw, !cnstrs)
		   in
		     EClo (Yw, comp (s, ss))
		   end
	       end
	       else (* s not patsub *)
                 (
		   EClo (X, invertSub (G, s, ss, rOccur))
		   handle NotInvertible => 
		     let 
		         (* val GY = Whnf.strengthen (ss, G) *)
                         (* shortcuts possible by invariants on G? *)
                         val GY = pruneCtx (ss, G, rOccur) (* prune or invert??? *)
                         (* val V' = EClo (V, comp (s, ss)) *)
		         val V' = pruneExp (G, (V, s), ss, rOccur) (* prune or invert??? *)
		         val Y = newEVar (GY, V')
		         val _ = addConstraint (cnstrs, ref (Eqn (G, EClo (X, s),
							             EClo (Y, Whnf.invert ss))))
		     in
		       Y
		     end
                 )
      | pruneExpW (G, (FgnExp csfe, s), ss, rOccur) =
          FgnExpStd.Map.apply csfe (fn U => pruneExp (G, (U, s), ss, rOccur))

      (* other cases impossible since (U,s1) whnf *)
    and pruneDec (G, (Dec (name, V), s), ss, rOccur) =
	  Dec (name, pruneExp (G, (V, s), ss, rOccur))
      | pruneDec (G, (NDec, _), _, _) = NDec
      (* Added for the meta level -cs Tue Aug 17 17:09:27 2004 *)
    and pruneSpine (G, (Nil, s), ss, rOccur) = Nil
      | pruneSpine (G, (App (U, S), s), ss, rOccur) = 
	  App (pruneExp (G, (U, s), ss, rOccur),
	       pruneSpine (G, (S, s), ss, rOccur))
      | pruneSpine (G, (SClo (S, s'), s), ss, rOccur) = 
	  pruneSpine (G, (S, comp (s', s)), ss, rOccur)
    and pruneHead (G, BVar k, ss, rOccur) = 
        (case (bvarSub (k, ss))
	   of Undef => raise Unify "Parameter dependency"
	    | Idx k' => BVar k')
      | pruneHead (G, H as Const _, ss, rOccur) = H
      | pruneHead (G, Proj (B as Bidx k, i), ss, rOccur) =
	(* blockSub (B, ss) should always be defined *)
	(* Fri Dec 28 10:03:12 2001 -fp !!! *)
	(case blockSub (B, ss)
	   of Bidx(k') => Proj (Bidx (k'), i))
      | pruneHead (G, H as Proj (LVar (r, sk, (l, t)), i), ss, rOccur) = 
        (* claim: LVar does not need to be pruned since . |- t : Gsome *)
	(* so we perform only the occurs-check here as for FVars *)
	(* Sat Dec  8 13:39:41 2001 -fp !!! *)
	(* this is not true any more, Sun Dec  1 11:28:47 2002 -cs  *)
	(* Changed from Null to G Sat Dec  7 21:58:00 2002 -fp *)
	   ( pruneSub (G, t, id, rOccur) ;
	     H )
      | pruneHead (G, H as Skonst _, ss, rOccur) = H
      | pruneHead (G, H as Def _, ss, rOccur) = H
      | pruneHead (G, FVar (x, V, s'), ss, rOccur) =
	  (* V does not to be pruned, since . |- V : type and s' = ^k *)
	  (* perform occurs-check for r only *)
	  (pruneExp (G, (V, id), id, rOccur);  (* why G here? -fp !!! *)
	   FVar (x, V, comp (s', ss)))
      | pruneHead (G, H as FgnConst _, ss, rOccur) = H
    (* pruneSub never allows pruning OUTDATED *)
    (* in the presence of block variables, this invariant 
       doesn't hold any more, because substitutions do not
       only occur in EVars any more but also in LVars!
       and there pruning is allowed!   Tue May 29 21:50:17 EDT 2001 -cs *)
    and pruneSub (G, s as Shift (n), ss, rOccur) =
        if n < ctxLength (G) 
	  then pruneSub (G, Dot (Idx (n+1), Shift (n+1)), ss, rOccur)
	else comp (s, ss)		(* must be defined *)
      | pruneSub (G, Dot (Idx (n), s'), ss, rOccur) =
	(case bvarSub (n, ss)
	   of Undef => raise Unify "Not prunable"
	    | Ft => Dot (Ft, pruneSub (G, s', ss, rOccur)))
      | pruneSub (G, Dot (Exp (U), s'), ss, rOccur) =
	  (* below my raise Unify *)
	  Dot (Exp (pruneExp (G, (U, id), ss, rOccur)),
	       pruneSub (G, s', ss, rOccur))
      (* pruneSub (G, Dot (Undef, s), ss, rOccur) is impossible *)
      (* By invariant, all EVars X[s] are such that s is defined everywhere *)
      (* Pruning establishes and maintains this invariant *)
    and pruneCtx (Shift n, Null, rOccur) = Null
      | pruneCtx (Dot (Idx k, t), Decl (G, D), rOccur) =
        let 
	  val t' = comp (t, invShift)
	  val D' = pruneDec (G, (D, id), t', rOccur)
	in
          Decl (pruneCtx (t', G, rOccur), D')
	end
      | pruneCtx (Dot (Undef, t), Decl (G, d), rOccur) = 
          pruneCtx (t, G, rOccur)
      | pruneCtx (Shift n, G, rOccur) = 
	  pruneCtx (Dot (Idx (n+1), Shift (n+1)), G, rOccur)
      (* ABP -- 3/1/05 *)
      | pruneCtx (Dot (Undef, t), Null, rOccur) = (print "ADAM555" ; raise Domain)
      | pruneCtx (Dot (Idx _, t), Null, rOccur) = (print "ADAM555" ; raise Domain)

    (* unifyExpW (G, (U1, s1), (U2, s2)) = ()
     
       Invariant:
       If   G |- s1 : G1   G1 |- U1 : V1    (U1,s1) in whnf
       and  G |- s2 : G2   G2 |- U2 : V2    (U2,s2) in whnf 
       and  G |- V1 [s1] = V2 [s2]  : L    (for some level L)
        ***** or V1 = V2 = kind  (needed to check type definitions)
        ***** added by kw Apr 5 2002
       and  s1, U1, s2, U2 do not contain any blockvariable indices Bidx
       then if   there is an instantiation I :  
                 s.t. G |- U1 [s1] <I> == U2 [s2] <I>
            then instantiation is applied as effect, () returned
	    else exception Unify is raised
       Other effects: EVars may be lowered
                      constraints may be added for non-patterns
    *)
    fun unifyExpW (G, Us1 as (FgnExp csfe1, _), Us2) =
          (case (FgnExpStd.UnifyWith.apply csfe1 (G, EClo Us2))
             of (Succeed residualL) =>
                  let
                    fun execResidual (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                          let
                            val W' = pruneExp (G, (W, id), ss, r)
                          in
                            instantiateEVar (r, W', !cnstrs)
                          end
                      | execResidual (Delay (U, cnstr)) =
                          delayExp ((U, id), cnstr)
                  in
                    List.app execResidual residualL
                  end
              | Fail => raise Unify "Foreign Expression Mismatch")

      | unifyExpW (G, Us1, Us2 as (FgnExp csfe2, _)) =
          (case (FgnExpStd.UnifyWith.apply csfe2 (G, EClo Us1))
             of (Succeed opL) =>
                  let
                    fun execOp (Assign (G, EVar(r, _, _, cnstrs), W, ss)) =
                          let
                            val W' = pruneExp (G, (W, id), ss, r)
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
	       if (i1 = i2) then (unifyBlock (G, b1, b2); unifySpine (G, (S1, s1), (S2, s2)))
	       else raise Unify "Global parameter clash"
	   | (Skonst(c1), Skonst(c2)) => 	  
	       if (c1 = c2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Skolem constant clash"
	   | (FVar (n1,_,_), FVar (n2,_,_)) =>
	       if (n1 = n2) then unifySpine (G, (S1, s1), (S2, s2))
	       else raise Unify "Free variable clash"
	   | (Def (d1), Def (d2)) =>
	       if (d1 = d2) then (* because of strict *) 
		 unifySpine (G, (S1, s1), (S2, s2))
	       else (*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
		 unifyDefDefW (G, Us1, Us2)
	   (* four new cases for defined constants *)
	   | (Def (d1), Const (c2)) =>
	     (case defAncestor d1
	        of Anc (_, _, NONE) => (* conservative *) unifyExpW (G, Whnf.expandDef Us1, Us2)
		 | Anc (_, _, SOME(c1)) =>
		   if (c1 = c2) then unifyExpW (G, Whnf.expandDef Us1, Us2)
		   else raise Unify "Constant clash")
	   | (Const (c1), Def (d2)) =>
	     (case defAncestor d2
                of Anc (_, _, NONE) => (* conservative *) unifyExpW (G, Us1, Whnf.expandDef Us2)
                 | Anc (_, _, SOME(c2)) =>
		   if (c1 = c2) then unifyExpW (G, Us1, Whnf.expandDef Us2)
		   else raise Unify "Constant clash")
           | (Def (d1), BVar (k2)) => raise Unify "Head mismatch" (* due to strictness! *)
	   | (BVar (k1), Def (d2)) => raise Unify "Head mismatch" (* due to strictness! *)
           (* next two cases for def/fgn, fgn/def *)
	   | (Def (d1), _) => unifyExpW (G, Whnf.expandDef Us1, Us2)
	   | (_, Def(d2)) => unifyExpW (G, Us1, Whnf.expandDef Us2)
           | (FgnConst (cs1, ConDec (n1, _, _, _, _, _)), FgnConst (cs2, ConDec (n2, _, _, _, _, _))) =>
               (* we require unique string representation of external constants *)
               if (cs1 = cs2) andalso (n1 = n2) then ()
               else raise Unify "Foreign Constant clash"
           | (FgnConst (cs1, ConDef (n1, _, _, W1, _, _, _)), FgnConst (cs2, ConDef (n2, _, _, V, W2, _, _))) =>
               if (cs1 = cs2) andalso (n1 = n2) then ()
               else unifyExp (G, (W1, s1), (W2, s2))
           | (FgnConst (_, ConDef (_, _, _, W1, _, _, _)), _) =>
               unifyExp (G, (W1, s1), Us2)
           | (_, FgnConst (_, ConDef (_, _, _, W2, _, _, _))) =>
               unifyExp (G, Us1, (W2, s2))              
	   | _ => raise Unify "Head mismatch")


      | unifyExpW (G, (Pi ((D1, _), U1), s1), (Pi ((D2, _), U2), s2)) =         
	  (unifyDec (G, (D1, s1), (D2, s2)) ;
	   unifyExp (Decl (G, decSub (D1, s1)), (U1, dot1 s1), (U2, dot1 s2)))

      | unifyExpW (G, Us1 as (Pi (_, _), _), Us2 as (Root (Def _, _), _)) =
	  unifyExpW (G, Us1, Whnf.expandDef (Us2))
      | unifyExpW (G, Us1 as  (Root (Def _, _), _), Us2 as (Pi (_, _), _)) =
	  unifyExpW (G, Whnf.expandDef (Us1), Us2)

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
		  val s' = intersection (s1,s2)	(* compute ss' directly? *)
		in
		  (* without the next optimization, bugs/hangs/sources.cfg
		     would gets into an apparent infinite loop
		     Fri Sep  5 20:23:27 2003 -fp 
		  *)
		  if Whnf.isId s' (* added for definitions Mon Sep  1 19:53:13 2003 -fp *)
		    then () (* X[s] = X[s] *)
		  else let val ss' = Whnf.invert s'
			   val V1' = EClo (V1, ss')  (* invertExp ((V1, id), s', ref NONE) *)
			   val G1' = Whnf.strengthen (ss', G1)
		       in
			 instantiateEVar (r1, EClo (newEVar (G1', V1'), s'), !cnstrs1)
		       end
		end
	      else addConstraint (cnstrs2, ref (Eqn (G, EClo Us2, EClo Us1)))
            else addConstraint (cnstrs1, ref (Eqn (G, EClo Us1, EClo Us2)))
	  else
	    if Whnf.isPatSub(s1) then 
	      let
		val ss1 = Whnf.invert s1
		val U2' = pruneExp (G, Us2, ss1, r1)
	      in
		(* instantiateEVar (r1, EClo (U2, comp(s2, ss1)), !cnstrs1) *)
		(* invertExpW (Us2, s1, ref NONE) *)
		instantiateEVar (r1, U2', !cnstrs1)
	      end
	    else if Whnf.isPatSub(s2) then 
	      let
		val ss2 = Whnf.invert s2
		val U1' = pruneExp (G, Us1, ss2, r2)
	      in
		(* instantiateEVar (r2, EClo (U1, comp(s1, ss2)), !cnstr2) *)
	        (* invertExpW (Us1, s2, ref NONE) *)
		instantiateEVar (r2, U1', !cnstrs2)
	      end
            else
              let
                val cnstr = ref (Eqn (G, EClo Us1, EClo Us2))
              in
                addConstraint (cnstrs1, cnstr)
              end

      | unifyExpW (G, Us1 as (EVar(r, GX, V, cnstrs), s), Us2 as (U2,s2)) =
	if Whnf.isPatSub(s) then
	  let val ss = Whnf.invert s
	      val U2' = pruneExp (G, Us2, ss, r)
	  in
	    (* instantiateEVar (r, EClo (U2, comp(s2, ss)), !cnstrs) *)
	    (* invertExpW (Us2, s, r) *)
	    instantiateEVar (r, U2', !cnstrs)
	  end
        else
          addConstraint (cnstrs, ref (Eqn (G, EClo Us1, EClo Us2)))

      | unifyExpW (G, Us1 as (U1,s1), Us2 as (EVar (r, GX, V, cnstrs), s)) =
	if Whnf.isPatSub(s) then 
	  let
	    val ss = Whnf.invert s
	    val U1' = pruneExp (G, Us1, ss, r)
	  in
	    (* instantiateEVar (r, EClo (U1, comp(s1, ss)), !cnstrs) *)
	    (* invertExpW (Us1, s, r) *)
	    instantiateEVar (r, U1', !cnstrs)
	  end
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

    and unifyDefDefW (G, Us1 as (Root (Def (d1), S1), s1), Us2 as (Root (Def (d2), S2), s2)) =
        (*  unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2)) *)
        let
	  val Anc (_, h1, c1Opt) = defAncestor d1
	  val Anc (_, h2, c2Opt) = defAncestor d2
	  val _ = case (c1Opt,c2Opt)
	            of (SOME(c1), SOME(c2)) =>
		       if c1 <> c2
			 then raise Unify ("Irreconcilable defined constant clash")
		       else ()
		     | _ => () (* conservative *)
	in
	  case Int.compare (h1, h2)
	    of EQUAL => unifyExpW (G, Whnf.expandDef (Us1), Whnf.expandDef (Us2))
             | LESS => unifyExpW (G, Us1, Whnf.expandDef (Us2))
	     | GREATER => unifyExpW (G, Whnf.expandDef (Us1), Us2)
	end

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
    (* conjecture: G == Null at all times *)
    (* Thu Dec  6 21:01:09 2001 -fp *)
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

    (* substitutions s1 and s2 were redundant here --- removed *)
    (* Sat Dec  8 11:47:12 2001 -fp !!! *)
    and unifyBlock (G, LVar (ref (SOME(B1)), s, _), B2) = unifyBlock (G, blockSub (B1, s), B2)
      | unifyBlock (G, B1, LVar (ref (SOME(B2)), s, _)) = unifyBlock (G, B1, blockSub (B2, s))
      | unifyBlock (G, B1, B2) = unifyBlockW (G, B1, B2)

    and unifyBlockW (G, LVar (r1, Shift(k1), (l1, t1)), LVar (r2, Shift(k2), (l2, t2))) = 
        if l1 <> l2 then
  	  raise Unify "Label clash"
        else
	  if r1 = r2
	    then ()
	  else
	    ( unifySub (G, t1, t2) ; (* Sat Dec  7 22:04:31 2002 -fp *)
	      (* invariant? always k1 = k2? *)
	      (* prune t2? Sat Dec  7 22:09:53 2002 *)
	      if k1 <> k2 then raise Bind else () ;
	      (*
	      if k1 < k2 then instantiateLVar (r1, LVar(r2, Shift(k2-k1), (l2, t2)))
		else instantiateLVar (r2, LVar(r1, Shift (k1-k2), (l1, t1)))
	      *)
	      let
		val ss = Whnf.invert (Shift(k1))
		val t2' = pruneSub (G, t2, ss, ref NONE) (* hack! *)
	      in
		instantiateLVar (r1, LVar(r2, Shift(0), (l2, t2'))) (* 0 = k2-k1 *)
	      end )

      | unifyBlockW (G, LVar (r1, s1, (l1, t1)),  B2) = 
	    (r1 := SOME (blockSub (B2, Whnf.invert s1)) ; ()) (* -- ABP *)
	    
      | unifyBlockW (G,  B1, LVar (r2, s2, (l2, t2))) = 
	    (r2 := SOME (blockSub (B1, Whnf.invert s2)) ; ()) (* -- ABP *)

(*      | unifyBlockW (G, LVar (r1, Shift(k1), (l1, t1)), Bidx i2) = 
	    (r1 := SOME (Bidx (i2 -k1)) ; ()) (* -- ABP *)

      | unifyBlockW (G, Bidx i1, LVar (r2, Shift(k2), (l2, t2))) = 
	    (r2 := SOME (Bidx (i1 -k2)) ; ()) (* -- ABP *)
*)
      (* How can the next case arise? *)
      (* Sat Dec  8 11:49:16 2001 -fp !!! *)      
      | unifyBlockW (G, Bidx (n1), (Bidx (n2))) =
	 if n1 <> n2
	   then raise Unify "Block index clash"
	 else ()


(*
      | unifyBlock (LVar (r1, _, _), B as Bidx _) = instantiate (r1, B) 
      | unifyBlock (B as Bidx _, LVar (r2, _, _)) = 

      This is still difficult --- B must make sense in the context of the LVar
      Shall we use the inverse of a pattern substitution? Or postpone as 
      a constraint if pattern substitution does not exist?
      Sun Dec  1 11:33:13 2002 -cs 
      
*)
    fun unify1W (G, Us1, Us2) =
          (unifyExpW (G, Us1, Us2); awakeCnstr (nextCnstr ()))

    and unify1 (G, Us1, Us2) =
          (unifyExp (G, Us1, Us2); awakeCnstr (nextCnstr ()))

    and awakeCnstr (NONE) = ()
      | awakeCnstr (SOME(ref Solved)) = awakeCnstr (nextCnstr ())
      | awakeCnstr (SOME(cnstr as ref (Eqn (G, U1, U2)))) =
          (solveConstraint cnstr;
           unify1 (G, (U1, id), (U2, id)))
      | awakeCnstr (SOME(ref (FgnCnstr csfc))) =
          if (FgnCnstrStd.Awake.apply csfc ()) then ()
          else raise Unify "Foreign constraint violated"

    fun unifyW (G, Us1, Us2) =
          (resetAwakenCnstrs (); unify1W (G, Us1, Us2))

    fun unify (G, Us1, Us2) =
          (resetAwakenCnstrs (); unify1 (G, Us1, Us2))

  in
    type unifTrail = unifTrail

    val reset = reset
    val mark = mark
    val unwind = unwind

    val suspend = suspend
    val resume = resume

    val delay = delayExp

    val instantiateEVar = instantiateEVar
    val instantiateLVar = instantiateLVar
    val addConstraint = addConstraint
    val solveConstraint = solveConstraint

    val intersection = intersection

    val unifyW = unifyW     
    val unify = unify
    val unifyBlock = unifyBlock

    val invertExp = invertExp
    val pruneExp = pruneExp

    fun invertible (G, Us, ss, rOccur) =
          (invertExp (G, Us, ss, rOccur); true)
          handle NotInvertible => false

    fun unifiable (G, Us1, Us2) =
          (unify (G, Us1, Us2); 
	   true)
          handle Unify msg =>  false

    fun unifiable' (G, Us1, Us2) = 
          (unify (G, Us1, Us2); NONE)
          handle Unify(msg) => SOME(msg)
  end
end;  (* functor Unify *)
