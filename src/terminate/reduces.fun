(* Reduction and Termination checker *)
(* revised version of deriving an order from a valid order predicate context  *) 
(* this implementation is based on ideas from the focusing calculus *)
(* Author: Carsten Schuermanm, Brigitte Pientka *)
(* checks if a type family reduces and terminates
   according to the given reduction order   
   
   %reduces O1 pred O2 callPattern

   check if call Pattern terminates under 02 
   check if call Pattern reduces according to O1 pred O2

 *)

(* *** note - this files subsumes terminates.fun  **** *)

functor Reduces    (structure Global : GLOBAL
		   structure IntSyn': INTSYN
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn'
	           structure Conv : CONV
		     sharing Conv.IntSyn = IntSyn'
	           structure Unify : UNIFY
		     sharing Unify.IntSyn = IntSyn'
(*	           structure Trail : TRAIL
		     sharing Trail.IntSyn = IntSyn' *)
	           structure Names : NAMES
		     sharing Names.IntSyn = IntSyn'
	           structure Index : INDEX
		     sharing Index.IntSyn = IntSyn'
	           structure Subordinate : SUBORDINATE
		     sharing Subordinate.IntSyn = IntSyn'
     		   structure Formatter : FORMATTER
	           structure Print : PRINT
		     sharing Print.IntSyn = IntSyn'
		     sharing Print.Formatter = Formatter
		   structure Order : ORDER
		     sharing Order.IntSyn = IntSyn'
		   structure Paths  : PATHS
		   structure Origins : ORIGINS
		     sharing Origins.Paths = Paths
		     sharing Origins.IntSyn = IntSyn'
	           structure CSManager : CS_MANAGER
		     sharing CSManager.IntSyn = IntSyn')
  :  REDUCES =
struct
  structure IntSyn = IntSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths
    structure N = Names
    structure F = Formatter
    structure R = Order

    datatype Quantifier =                     (* Quantifier to mark parameters *)
      Universal                               (* Q ::= Uni                     *)
    | Existential                             (*     | Ex                      *)

    (* If Q marks all parameters in a context G we write   G : Q               *)

    datatype 'a Predicate = 
      Less of 'a * 'a
    | Leq of 'a * 'a 
    | Eq of 'a * 'a 
    | Pi of I.Dec * 'a Predicate       

    exception Error' of P.occ * string

    fun error (c, occ, msg) =  
        (case Origins.originLookup c
	   of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) => 
		raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                                         Origins.linesInfoLookup (fileName),
                                         msg)))

   fun union (I.Null, G) = G
     | union (G, I.Null) = G
     | union (G, I.Decl(G', P)) = 
         union (I.Decl(G, P), G')

   (* shifting substitutions *)

   (* shiftO f O = O'
    if O is an order 
      then we shift the substitutions which are associated
	with its terms by applying f to it
    *)

    fun shiftO (R.Arg ((U, us), (V, vs))) f = 
	    R.Arg ((U, (f us)), (V, (f vs)))
      | shiftO (R.Lex L) f = R.Lex (map (fn O => shiftO O f) L)
      | shiftO (R.Simul L) f = R.Simul (map (fn O => shiftO O f) L)

    fun shiftP (Less(O1, O2)) f = Less(shiftO O1 f, shiftO O2 f)
      | shiftP (Leq(O1, O2)) f = Leq(shiftO O1 f, shiftO O2 f)
      | shiftP (Eq(O1, O2)) f = Eq(shiftO O1 f, shiftO O2 f)
      | shiftP (Pi(D, P)) f = Pi(D, shiftP P f)      

    fun shiftCtx I.Null f = I.Null
      | shiftCtx (I.Decl(RG, P)) f =
	  I.Decl(shiftCtx RG f, shiftP P f)
	
    (* formatting *)

  fun fmtFront (G, I.Idx i) = F.Hbox [F.String "I.Idx (" , F.String (Int.toString i) , F.String ")"]
      | fmtFront (G, I.Exp e) = F.Hbox [F.String "I.Exp (" ,Print.formatExp(G, e) , F.String ")"]
      | fmtFront (G, I.Undef) = F.Hbox [F.String "I.Undef"]

    fun fmtSubst (G, I.Shift n) = F.Hbox [F.String "I.Shift ", F.String (Int.toString n)]
      | fmtSubst (G, I.Dot(Ft, s)) = F.Hbox [F.String "I.Dot(" , fmtFront (G, Ft) , F.String  ", " ,
						fmtSubst (G,s), F.String  ")"]

    fun fmtSpine (G, I.Nil) = F.Hbox [F.String " I.Nil" ]
      | fmtSpine (G, I.App(e, spine)) = 
          F.Hbox [F.String "I.App ( ", Print.formatExp(G, e), F.String ", ", 
		  fmtSpine (G, spine), F.String " )" ]
      | fmtSpine (G, I.SClo (spine, S)) = 
	  F.Hbox [F.String "I.SClo ( ", fmtSpine (G, spine), F.String ", ", 
		  fmtSubst (G, S), F.String " )"]


    fun fmtSpine (G, I.Nil) = F.Hbox [F.String " I.Nil" ]
      | fmtSpine (G, I.App(U, spine)) = 
          F.Hbox [F.String "I.App ( ", Print.formatExp(G, U), F.String ", ", 
		  fmtSpine (G, spine), F.String " )" ]
      | fmtSpine (G, I.SClo (spine, S)) = 
	  F.Hbox [F.String "I.SClo ( ", fmtSpine (G, spine), F.String ", ", 
		  fmtSubst (G, S), F.String " )"]

    fun fmtOrder (G, O) =
        let
	  fun fmtOrder' (R.Arg (Us as (U, s), Vs as (V, s'))) =
	        F.Hbox [F.String "(", Print.formatExp (G, I.EClo Us), F.String ")"]
	    | fmtOrder' (R.Lex L) =
		F.Hbox [F.String "{", F.HOVbox0 1 0 1 (fmtOrders L), F.String "}"]
	    | fmtOrder' (R.Simul L) =
		F.Hbox [F.String "[", F.HOVbox0 1 0 1 (fmtOrders L), F.String "]"]
	  
	  and fmtOrders [] = []
	    | fmtOrders (O :: []) = fmtOrder' O :: []
	    | fmtOrders (O :: L) = fmtOrder' O :: F.Break :: fmtOrders L
	in
	  fmtOrder' O
	end

    fun fmtComparison (G, O, comp, O') =
        F.HOVbox0 1 0 1 [fmtOrder (G, O), F.Break, F.String comp, F.Break, fmtOrder (G, O')]

    fun fmtPredicate (G, Less(O, O')) = fmtComparison (G, O, "<", O')
      | fmtPredicate (G, Leq(O, O'))  = fmtComparison (G, O, "<=", O')
      | fmtPredicate (G, Eq(O, O'))  = fmtComparison (G, O, "=", O')
      | fmtPredicate (G, Pi(D, P))  =  (* F.String "Pi predicate"  *)
          F.Hbox [F.String "Pi ", fmtPredicate (I.Decl(G, D), shiftP P (fn s => I.dot1 s))]

    fun fmtDerive (G, P, P') = 
	print ("\n derive: " ^ 
	       F.makestring_fmt (fmtPredicate(G, P))  
	       ^ " |- " ^ F.makestring_fmt (fmtPredicate(G, P')) ^  "\n")

    fun fmtRGCtx (G, I.Null) = ""
      | fmtRGCtx (G, I.Decl(I.Null, P)) = 
	F.makestring_fmt(fmtPredicate (G, P) )
      | fmtRGCtx (G, I.Decl(RG, P)) = 
	F.makestring_fmt(fmtPredicate (G, P)) ^ " ," ^ fmtRGCtx(G, RG)

    (* substitute (G, Q, M, X, N, sc) = M'

         M[X]    and 
         M' = M[y]
     *)
    fun subst (G, M as ((U, us), (V, vs)), I.BVar n , N) = 
      let
	fun shifts (0, s) = s
	  | shifts (n, s) = shifts(n-1, I.Dot(I.Idx (n), s))
	val s' = shifts (n - 1, I.Dot(I.Exp(N), I.Shift n))	    
      in 
	((U, I.comp(us, s')), (V, I.comp(vs, s')))
      end 


    fun substO (G, R.Arg UsVs, X, N) = R.Arg (subst (G, UsVs, X, N))
      | substO (G, R.Lex L, X, N) = R.Lex (map (fn O => substO (G, O, X, N)) L)
      | substO (G, R.Simul L, X, N) = R.Simul (map (fn O => substO (G, O, X, N)) L)
         
    fun substP (G, Eq(O, O'), X, N) = 
          Eq(substO (G, O, X, N), substO(G, O', X, N))
      | substP (G, Less (O, O'), X, N) = 
          Less(substO (G, O, X, N), substO(G, O', X, N))
      | substP (G, Leq (O, O'), X, N) = 
          Leq(substO (G, O, X, N), substO(G, O', X, N))
      | substP (G, Pi(D as I.Dec(_, V), P'), X, N) = 
	  Pi(D, substP (G, P', X, N))

    fun substCtx (G, TG, X, N) = 
      let 
	fun substCtx' (TG, I.Null, _, _) = TG
	  | substCtx' (TG, I.Decl(TG', P), X, N) = 
  	      substCtx' (I.Decl(TG, substP (G, P, X, N)), TG', X,  N)
      in 
       substCtx' (I.Null, TG, X, N)
      end

    (* select (c, (S, s)) = P
      
       select parameters according to termination order        

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi 
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
    fun select (c, (S, s)) =
        let 
	  val SO = R.selLookup c 
	  val Vid = (I.constType c, I.id)
	  fun select'' (n, (Ss', Vs'')) =
	        select''W (n, (Ss', Whnf.whnf Vs''))
	  and select''W (1, ((I.App (U', S'), s'), 
			     (I.Pi ((I.Dec (_, V''), _), _), s''))) = 
	        ((U', s'), (V'', s''))
	    | select''W (n, ((I.SClo (S', s1'), s2'), Vs'')) =
		select''W (n, ((S', I.comp (s1', s2')), Vs''))
	    | select''W (n, ((I.App (U', S'), s'), 
			     (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) = 
		select'' (n-1, ((S', s'), 
				(V2'', I.Dot (I.Exp (I.EClo (U', s')), s''))))
	  fun select' (R.Arg n) = R.Arg (select'' (n, ((S, s), Vid)))
	    | select' (R.Lex L) = R.Lex (map select' L)
	    | select' (R.Simul L) = R.Simul (map select' L)
	in
	  select' (R.selLookup c)
	end

    fun selectOcc (c, (S, s), occ) =
        select (c, (S, s))
	handle R.Error (msg) =>
	  raise Error' (occ, "Termination violation: no order assigned for " ^ N.qidToString (N.constQid c))

    (* selectROrder (c, (S, s)) = P
       
       select parameters according to reduction order

       Invariant:
       If   . |- c : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] according to sel (c)
       and  G |- si : Gi  Gi |- Ui : Vi 
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
    fun selectROrder (c, (S, s)) =
        let 
	  val Vid = (I.constType c, I.id)
	  fun select'' (n, (Ss', Vs'')) =
	        select''W (n, (Ss', Whnf.whnf Vs''))
	  and select''W (1, ((I.App (U', S'), s'), 
			     (I.Pi ((I.Dec (_, V''), _), _), s''))) = 
	        ((U', s'), (V'', s''))
	    | select''W (n, ((I.SClo (S', s1'), s2'), Vs'')) =
		select''W (n, ((S', I.comp (s1', s2')), Vs''))
	    | select''W (n, ((I.App (U', S'), s'), 
			     (I.Pi ((I.Dec (_, V1''), _), V2''), s''))) = 
		select'' (n-1, ((S', s'), 
				(V2'', I.Dot (I.Exp (I.EClo (U', s')), s''))))
	    | select''W _ = raise Error ("this case should not happen")
	  fun select' (R.Arg n) = R.Arg (select'' (n, ((S, s), Vid)))
	    | select' (R.Lex L) = R.Lex (map select' L)
	    | select' (R.Simul L) = R.Simul (map select' L)

	  fun selectP (R.Less(O1, O2)) = Less(select' O1, select' O2)
	    | selectP (R.Leq(O1, O2)) = Leq(select' O1, select' O2)
	    | selectP (R.Eq(O1, O2)) = Eq(select' O1, select' O2)
	in
	  selectP (R.selLookupROrder c) 
	end

    fun selectROrderOcc (c, (S, s), occ) =
        selectROrder (c, (S, s))
	handle R.Error (msg) =>
	  raise Error' (occ, "Reduction violation: no order assigned for " ^ N.qidToString (N.constQid c))

    fun conv ((Us, Vs), (Us', Vs')) =
        Conv.conv (Vs, Vs') andalso  
	Conv.conv (Us, Us') 

    (* eq (G, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2] 
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)
    fun eq (G, (Us, Vs), (Us', Vs'), sc) = 
      CSManager.trail (fn () =>
		       Unify.unifiable (G, Vs, Vs')
		       andalso Unify.unifiable (G, Us, Us')
		       andalso sc ())

    (* init () = true 

       Invariant:
       The inital constraint continuation
    *)
    fun init () = true

    fun isUniversal (Universal) = true
      | isUniversal (Existential) = false

    fun isExistential (Universal) = false
      | isExistential (Existential) = true


    (* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q 
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
    fun isParameter (Q, X) = isParameterW (Q, Whnf.whnf (X, I.id))

    and isParameterW (Q, Us) = 
        isUniversal (I.ctxLookup (Q, Whnf.etaContract (I.EClo Us)))
	handle Whnf.Eta => isFreeEVar (Us)
 
   (* isFreeEVar (Us) = true
       iff Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
    and isFreeEVar (I.EVar (_, _, _,ref []), _) = true   (* constraints must be empty *)
      | isFreeEVar (I.Lam (D, U), s) = isFreeEVar (Whnf.whnf (U, I.dot1 s))
      | isFreeEVar _ = false

    (* isAtomic (G, X) = true 
       Invariant: 
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter

      (* -bp  not sure, if this is right ... *)
     *)
    fun isAtomic(G, Q, Us) = isAtomicW (G, Q, Whnf.normalize Us)
    and isAtomicW (G, Q, (X as (I.Root (I.Const c, I.Nil)))) = true
      | isAtomicW (G, Q, (X as (I.Root (I.BVar n, I.Nil)))) =
          true
      | isAtomicW (G, Q, (X as (I.Root (I.BVar n, S)))) = 
	  isExistential(I.ctxLookup (Q, n))
      | isAtomicW (G, Q, (X as (I.EClo _))) = true   (* existential var *)
      | isAtomicW (G, Q, _) = false

    fun AtomicNotP (G, Q, Us as (U, s)) = 
	isAtomic(G, Q, Us) andalso not(isParameter(Q, I.EClo(Us)))

    fun isActiveL (Less (R.Lex O, R.Lex O')) = true
      | isActiveL (Less (R.Simul O, R.Simul O')) = true
      | isActiveL (Less (R.Arg _, R.Arg ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)))) = true
      | isActiveL (Less (R.Arg _, R.Arg (Us' as (I.Root _, s'), Vs'))) = true
      | isActiveL (Leq (R.Arg _, R.Arg ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)))) = true
      | isActiveL (Leq (R.Lex O, R.Lex O')) = true
      | isActiveL (Leq (R.Simul O, R.Simul O')) = true
      | isActiveL (Eq (R.Lex _, R.Lex _)) = true
      | isActiveL (Eq (R.Simul _, R.Simul _)) = true
      | isActiveL (Eq (R.Arg ((I.Lam _, _), _), R.Arg ((I.Lam _, _),_ ))) = false 
      | isActiveL (Eq (R.Arg UsVs, R.Arg UsVs')) = true
      | isActiveL (Pi (D, P)) = false
(*      | isActiveL _ = true *)

    (* ltRA (G, Q, TG, PG, O, O', sc) = B' *)
    fun ltRA (G, Q, TG, PG, UsVs, UsVs', sc) = 
	 ltRAW (G, Q, TG, PG, Whnf.whnfEta UsVs, UsVs', sc) 

    and ltRAW (G, Q, TG, PG, ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), 
	      ((U', s1'), (V', s2')), sc) = 
	ltRA (I.Decl (G, N.decLUName (G, I.decSub (D, s2))),
	     I.Decl (Q, Universal), shiftCtx TG (fn s => I.comp(s, I.shift)), 
	      shiftCtx PG (fn s => I.comp(s,I.shift)),
	     ((U, I.dot1 s1), (V, I.dot1 s2)), 
	     ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), sc)
      | ltRAW (G, Q, TG, PG, UsVs, UsVs' ,sc) = 
	(* UsVs any term of base type *)
	focusL (G, Q, TG, PG, Less(R.Arg UsVs, R.Arg UsVs'), sc)

    (* leRA (G, Q, TG, PG, O, O', sc) = B' *)
    and leRA (G, Q, TG, PG, UsVs, UsVs', sc) = 
	leRAW (G, Q, TG, PG, Whnf.whnfEta UsVs, UsVs', sc)
    and leRAW (G, Q, TG, PG, ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), 
	      ((U', s1'), (V', s2')), sc) = 
	leRA (I.Decl (G, N.decLUName (G, I.decSub (D, s2))),
	     I.Decl (Q, Universal), shiftCtx TG (fn s => I.comp(s,I.shift)),
	      shiftCtx PG (fn s => I.comp(s,I.shift)),  
	     ((U, I.dot1 s1), (V, I.dot1 s2)), 
	     ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), sc)
      | leRAW (G, Q, TG, PG, UsVs, UsVs' ,sc) = 
	(* UsVs any term of base type *)
	focusL (G, Q, TG, PG, Leq(R.Arg UsVs, R.Arg UsVs'), sc)

    (* eqRA (G, Q, TG, PG, O, O', sc) = B' 
       O, O' need to be structurally equal *)
    and eqRA (G, Q, TG, PG, UsVs as (Us, Vs), UsVs' as (Us', Vs'), sc) = 
        eqRAW (G, Q, TG, PG, Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', sc)

    and eqRAW (G, Q, TG, PG, (Us as (I.Lam (D as I.Dec (_, V1'), U'), s1'), 
			      Vs as (I.Pi ((I.Dec (_, V2'), _), V'), s2')), 
	     (Us' as (I.Lam (D' as I.Dec (_, V1''), U''), s1''), 
	      Vs' as (I.Pi ((I.Dec (_, V2''), _), V''), s2'')), sc) = 
	  eqRA (I.Decl (G, N.decLUName (G, I.decSub (D, s1'))),
	       I.Decl (Q, Universal), shiftCtx TG (fn s => I.comp(s, I.shift)), 
		shiftCtx PG (fn s => I.comp(s,I.shift)),
	       ((U', I.dot1 s1'), (V', I.dot1 s2')),
	       ((U'', I.dot1 s1''),(V'', I.dot1 s2'')), sc)
    | eqRAW (G, Q, TG, PG, UsVs as ((I.Root (I.Const c, S'), s'), Vs), 
	     UsVs' as ((I.Root (I.Const c1, S1), s1), Vs'), sc) = 
	if (isAtomic (G, Q, (I.Root (I.Const c, S'), s')) orelse 
	    isAtomic (G, Q, (I.Root (I.Const c1, S1), s1))) then
	  focusL (G, Q, TG, PG, Eq(R.Arg UsVs, R.Arg UsVs'), sc)
	else 
	  (if c = c1 then 
	     eqSpineRA (G, Q, TG, PG, ((S', s'),(I.constType c, I.id)), 
			((S1, s1),(I.constType c1, I.id)), sc)
	    else 
	      false  (* ? - bp *))
      | eqRAW (G, Q, TG, PG, UsVs as ((I.Root (I.BVar c, S'), s'), Vs),
	      UsVs' as ((I.Root (I.BVar c1, S1'), s1'), Vs'), sc) = 
	  let 
	    val I.Dec (_, V') = I.ctxDec (G, c)
	    val I.Dec (_, V1') = I.ctxDec (G, c1)	
	  in
	     if (isAtomic(G, Q, (I.Root (I.BVar c, S'), s')) orelse (* atomic term not a param. *)
		 isAtomic(G, Q, (I.Root (I.BVar c1, S1'), s1'))) then
	       focusL(G, Q, TG, PG, Eq(R.Arg UsVs, R.Arg UsVs'), sc)
	     else 		
	       ((c = c1)         
		andalso 
		eqSpineRA (G, Q, TG, PG, ((S', s'), (V', I.id)), ((S1', s1'), (V1', I.id)), sc)) 
	  end 

      | eqRAW (G, Q, TG, PG, UsVs, UsVs', sc) = 
       (* -bp TG, PG --> M = s N  should not be provable *)
	    focusL (G, Q, TG, PG, Eq(R.Arg UsVs, R.Arg UsVs'), sc)

    and eqSpineRA (G, Q, TG, PG, (Us, Vs), (Us', Vs'), sc) = 
          eqSpineRAW (G, Q, TG, PG, (Us, (Whnf.whnf Vs)), (Us', (Whnf.whnf Vs')), sc) 

          (* normalize Spines ...  eqSpineRAW (G, Q, TG, PG, (Us, Vs), (Us', Vs'), sc) - bp*)

    and eqSpineRAW (G, Q, TG, PG, ((I.Nil, s'), Vs'), ((I.Nil, s1'), V1s), sc) = 
          sc()
      | eqSpineRAW (G, Q, TG, PG, ((I.SClo (S, s'), s''), Vs' as (V, s)), SV1s, sc) = 
	  eqSpineRA (G, Q, TG, PG, ((S, I.comp (s', s'')), Vs'), SV1s, sc)

      | eqSpineRAW (G, Q, TG, PG, SVs, ((I.SClo (S1, s1'), s1''), V1s' as (V1, s1)), sc) = 
	  eqSpineRA (G, Q, TG, PG, SVs, ((S1, I.comp (s1', s1'')), V1s'), sc)

      | eqSpineRAW (G, Q, TG, PG, ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
		  ((I.App (U'', S''), s1''), (I.Pi ((I.Dec (_, V1''), _), V2''), s2'')), sc) = 
	eqRA (G, Q, TG, PG, ((U', s1'), (V1', s2')), ((U'', s1''), (V1'', s2'')), sc)
	andalso 
	eqSpineRA (G, Q, TG, PG, ((S',s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
		  ((S'',s1''), (V2'', I.Dot (I.Exp (I.EClo (U'', s1'')), s2''))), sc)
      | eqSpineRAW (G, Q, TG, PG, ((U, s), Vs), ((U', s'), Vs'), sc) = 
	((if (!Global.chatter) > 6 then  
	    print (" \n should never happen - " ^ F.makestring_fmt(fmtSpine (G, U)) ^ 
		   " = " ^ F.makestring_fmt(fmtSpine (G, U')))
	  else
	    ());
         false)

     (* ltLexRA (G, Q, TG, PG, L1, L2, sc) = B'
     
       InvaRAiant:
       If   G : Q and  (PG) is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff L1 is lexically smaller than L2 
    *)
    and ltLexRA (G, Q, TG, PG, [], [], sc) = false
      | ltLexRA (G, Q, TG, PG, O :: L, O' :: L', sc) =
          activeR (G, Q, TG, PG, Less(O, O'), sc) 
	  orelse 
	  (activeR (G, Q, TG, PG, Eq(O, O'), sc) andalso ltLexRA (G, Q, TG, PG, L, L', sc))
      
    (* eqLexRA (G, Q, TG, PG, Olist, Olist, sc) = B *)
    and eqLexRA (G, Q, TG, PG, [], [], sc) = sc()
      | eqLexRA (G, Q, TG, PG, (O::L), (O'::L'), sc) = 
          activeR (G, Q, TG, PG, Eq(O, O'), sc)
	  andalso 
	  eqLexRA (G, Q, TG, PG, L, L', sc)

    (* eqSimulRA (G, Q, TG, PG, Olist, Olist, sc) = B *)
    and eqSimulRA (G, Q, TG, PG, [], [], sc) = sc()
      | eqSimulRA (G, Q, TG, PG, (O::L), (O'::L'), sc) = 
          activeR (G, Q, TG, PG, Eq(O, O'), sc)
	  andalso 
	  eqSimulRA (G, Q, TG, PG, L, L', sc)

    (* activeR (G, Q, TG, PG,  P, sc) = B'
     Invariant:
       If   G : Q and 
            G: PG  where PG is context of passive reduction assumptions
            G: AG  where AG is context of active reduction assumptions
       and  G |- P is a order predicate
       then B' holds iff  PG, RG |- P 
     *)
    and activeR (G, Q, TG, PG, Eq(R.Simul O, R.Simul O'), sc) = 
	  eqSimulRA (G, Q, TG, PG, O, O', sc)
      | activeR (G, Q, TG, PG, Eq(R.Lex O, R.Lex O'), sc) = 
	  eqLexRA (G, Q, TG, PG, O, O', sc)
      | activeR (G, Q, TG, PG, P as Eq(R.Arg UsVs, R.Arg UsVs'), sc) = 
          eqRA (G, Q, TG, PG, UsVs, UsVs', sc)
      | activeR (G, Q, TG, PG, P as Less(R.Arg UsVs, R.Arg UsVs'), sc) = 
	  ltRA (G, Q, TG, PG, UsVs, UsVs', sc)
      | activeR (G, Q, TG, PG, P as Leq(R.Arg UsVs, R.Arg UsVs'), sc) = 
	  leRA (G, Q, TG, PG, UsVs, UsVs', sc)
      | activeR (G, Q, TG, PG, P, sc) = 
	  ((if (!Global.chatter) > 6 then  
	      print ("\n transition to focusL \n" ^ 
		     "focusL: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^
		     " L==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	    else 
	      ());
	    focusL (G, Q, TG, PG, P, sc))

    and ltLexRF (G, Q, TG, [], [], sc) = true
      | ltLexRF (G, Q, TG, O :: L, O' :: L', sc) = 
          (activeR (G, Q, TG, I.Null, Less(O, O'), sc)
           orelse
	   (activeR (G, Q, TG, I.Null, Eq(O, O'), sc) andalso ltLexRF (G, Q, TG, L, L', sc)))

  (* ltSimulRF (G, Q, TG, PG, L1, L2) = B'
     
       Invariant:
       If   G : Q and (PG) is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously smaller than L2 
    *)
    and ltSimulRF (G, Q, TG, [], [], sc) = true
      | ltSimulRF (G, Q, TG, O :: L, O' :: L', sc) = 
         (activeR (G, Q, TG, I.Null, Less(O, O'), sc) andalso leSimulRF (G, Q, TG, L, L', sc))
	  orelse 	  
	  (activeR (G, Q, TG, I.Null, Eq(O, O'), sc) andalso ltSimulRF (G, Q, TG, L, L', sc))
	   

    (* leSimulRF (G, Q, TG, L1, L2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously less than or equal to L2 
    *)
    and leSimulRF (G, Q, TG, [], [], sc) = sc ()
      | leSimulRF (G, Q, TG, O :: L, O' :: L', sc) =
          activeR (G, Q, TG, I.Null, Leq(O, O'), sc) 
	  andalso 
	  leSimulRF (G, Q, TG, L, L', sc) 

    (* eqSimulRF (G, Q, TG, L1, L2) = B'
     
       Invariant:
       If   G : Q and (PG) is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is convertible to L2 
    *)
    and eqSimulRF (G, Q, TG, [], [], sc) = sc()
      | eqSimulRF (G, Q, TG, O :: L, O' :: L', sc) = 
          focusR (G, Q, TG, Eq(O, O'), sc) 
	  andalso eqSimulRF (G, Q, TG, L, L', sc)

  (* eqLexRF (G, Q, TG, L1, L2) = B'
     
       Invariant:
       If   G : Q and (TG) is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is convertible to L2 
    *)
   and eqLexRF (G, Q, TG, [], [], sc) = sc()
      | eqLexRF (G, Q, TG, O :: L, O' :: L', sc) = 
          focusR (G, Q, TG, Eq(O, O'), sc) 
	  andalso eqLexRF (G, Q, TG, L, L', sc)

   (* ltRF (G, Q, TG, UsVs, UsVs' ,sc = B *)
   and ltRF (G, Q, TG, UsVs, UsVs', sc) = 
	ltRFW (G, Q, TG, UsVs, Whnf.whnfEta UsVs', sc)

   and ltRFW (G, Q, TG, UsVs as (Us, (V,s)), 
	      ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	       (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc) = 
         (if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	    let  (* enforce that X is only instantiated to parameters *) 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      val sc' = fn () => (isParameter (Q, X) andalso sc ())    
	    in
	       ltRF (G, Q, TG, UsVs, ((U', I.Dot (I.Exp (X), s1')), 
				      (V', I.Dot (I.Exp (X), s2'))), sc')
	    end
	  else
	    if Subordinate.below (I.targetFam V1', I.targetFam V) then
	      let 
		val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      in
		ltRF (G, Q, TG, UsVs, ((U', I.Dot (I.Exp (X), s1')), 
				       (V', I.Dot (I.Exp (X), s2'))),sc)
	      end
	    else true)(* possibly redundant if lhs always subordinate to rhs *)

     | ltRFW (G, Q, TG, UsVs, (Us' as (I.Root (I.Const c, S'), s'), Vs'), sc) = 
	if isAtomic (G, Q, (I.Root (I.Const c, S'), s')) then (* atomic term not a param. *)
	  ((if (!Global.chatter) > 6 then  
	    print ("\n atomic const - transition to focusT \n" ^ 
		   "focusT: " ^ fmtRGCtx(G, TG) ^
		   " L==>" ^  F.makestring_fmt (fmtPredicate(G, Less(R.Arg UsVs, R.Arg (Us', Vs'))))
		     ^"\n")
	  else 
	    ());
	  false )
	  (*  -bp8/7/00. focusT (G, Q, TG, Less(R.Arg UsVs, R.Arg (Us', Vs')), sc)) *)
	else 
	  ltSpineRF (G, Q, TG, UsVs,((S', s'), (I.constType c, I.id)), sc)

     | ltRFW (G, Q, TG, UsVs, (Us' as (I.Root (I.BVar c, S'), s'), Vs'), sc) = 
	let 
	  val I.Dec (_, V') = I.ctxDec (G, c)
	in
	  if isAtomic(G, Q, (I.Root (I.BVar c, S'), s')) then
	    (if isParameter(Q, I.EClo((I.Root (I.BVar c, S')), s')) then (* atomic term not a param. *)
	        false
	     else 		
	       ((if (!Global.chatter) > 6 then  
		     print ("\n atomic bvar - transition to focusT \n" ^ 
			    "focusT: " ^ fmtRGCtx(G, TG) ^
			    " L==>" ^  F.makestring_fmt (fmtPredicate(G, Less(R.Arg UsVs, R.Arg (Us', Vs'))))
				^"\n")
		 else 
		 ());
		focusT (G, Q, TG, Less(R.Arg UsVs, R.Arg (Us', Vs')), sc)))
	  else 
	    ltSpineRF (G, Q, TG, UsVs, ((S', s'), (V', I.id)), sc)
	end 
      | ltRFW (G, Q, TG, UsVs, UsVs', sc) = 
	((if (!Global.chatter) > 6 then  
	    print ("\n should not happen !!! ltRFW - transition to focusT'\n" ^ fmtRGCtx(G, TG) ^
		   " T-->" ^  F.makestring_fmt (fmtPredicate(G, Less(R.Arg UsVs, R.Arg UsVs')))
		     ^"\n")
	  else ());
	   focusT' (G, Q, I.Null, TG, Less(R.Arg UsVs, R.Arg UsVs'), sc))

    and ltSpineRF (G, Q, TG, UsVs, (Ss', Vs'), sc) = 
	ltSpineRFW (G, Q, TG, UsVs, (Ss', Whnf.whnf Vs'), sc)
    and ltSpineRFW (G, Q, TG, UsVs, ((I.Nil, _), _), sc) = 
          false
      | ltSpineRFW (G, Q, TG, UsVs, ((I.SClo (S, s'), s''), Vs'), sc) =
	ltSpineRFW (G, Q, TG, UsVs, ((S, I.comp (s', s'')), Vs'), sc) 
      | ltSpineRFW (G, Q, TG, UsVs, 
		    ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc) = 
	(leRF (G, Q, TG, UsVs, ((U', s1'), (V1', s2')), sc)
	 orelse 
	 ltSpineRFW (G, Q, TG, UsVs, 
		     ((S', s1'),(V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc))
    
    (* leRF (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = B *) 
    and leRF (G, Q, TG, UsVs, UsVs', sc) = 
           leRFW (G, Q, TG, UsVs, Whnf.whnfEta UsVs', sc)
    and leRFW (G, Q, TG, UsVs as (Us, (V, s)), 
	      ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	       (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc) = 
         (if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	    let  (* enforce that X is only instantiated to parameters *) 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      val sc' = fn () => (isParameter (Q, X) andalso sc ())    
	    in
	      leRF (G, Q, TG, UsVs, ((U', I.Dot (I.Exp (X), s1')), 
				     (V', I.Dot (I.Exp (X), s2'))), sc')
	    end
	  else
	    if Subordinate.below (I.targetFam V1', I.targetFam V) then
	      let 
		val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
 	      in
		leRF (G, Q, TG, UsVs, ((U', I.Dot (I.Exp (X), s1')), 
				       (V', I.Dot (I.Exp (X), s2'))),sc)
	      end
	    else true (* possibly redundant if lhs always subordinate to rhs *))
      | leRFW (G, Q, TG, UsVs as ((I.Root _, _), Vs), 
	      UsVs' as ((I.Root _, _), Vs'), sc) = 
	(activeR (G, Q, TG, I.Null, Eq(R.Arg UsVs, R.Arg UsVs'), sc)
	 orelse
	 ltRF (G, Q, TG, UsVs, UsVs', sc))
      | leRFW (G, Q, TG, UsVs, UsVs', sc) = 
	(* should not happen *) false

    (* focusR (G, Q, TG, P, sc) = B *)
    and focusR (G, Q, TG, Less(R.Simul O, R.Simul O'), sc) = 
	  ltSimulRF (G, Q, TG, O, O', sc)
      | focusR (G, Q, TG, Less(R.Lex O, R.Lex O'), sc) = 
	  ltLexRF (G, Q, TG, O, O', sc)
      | focusR (G, Q, TG, Less(R.Arg UsVs, R.Arg UsVs'), sc) = 
	  ltRF (G, Q, TG, UsVs, UsVs', sc)
      | focusR (G, Q, TG, Leq(R.Simul O, R.Simul O'), sc) = 
	  ltSimulRF (G, Q, TG, O, O', sc)
	  orelse	  
	  eqSimulRF (G, Q, TG, O, O', sc)
      | focusR (G, Q, TG, Leq(R.Lex O, R.Lex O'), sc) = 
	  ltLexRF (G, Q, TG, O, O', sc)
	  orelse
	   eqLexRF (G, Q, TG, O, O', sc)
      | focusR (G, Q, TG, Leq(R.Arg UsVs, R.Arg UsVs'), sc) = 	   
	   leRF (G, Q, TG, UsVs, UsVs', sc)
      | focusR (G, Q, TG, P, sc) = 
	   ((if (!Global.chatter) > 6 then  
	      print ("\n fails in focusR because multiplicity might not be high enough!\n")
	     else ());
	   false)
        (* should never happen this case 
           - if multiplicity > 1 then transition to focusL *)
		 
    (* invariant: UsVs' is AtomicNotp *)
    and ltLF (G, Q, TG, PG, UsVs, UsVs', P, sc) = 
	ltLFW (G, Q, TG, PG, Whnf.whnfEta UsVs, UsVs', P, sc)
    and ltLFW (G, Q, TG, PG, 
	       ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
		(I.Pi ((I.Dec (_, V2'), _), V'), s2')), UsVs as (Us, (V,s)), P, sc) = 
	  (if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	     let  (* enforce that X is only instantiated to parameters *) 
	       val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	       val sc' = fn () => (isParameter (Q, X); sc ())    
	     in
	       ltLF (G, Q, TG, PG, ((U', I.Dot (I.Exp (X), s1')), 
				     (V', I.Dot (I.Exp (X), s2'))),
		     UsVs, P, sc')
	     end
	   else
	     if Subordinate.below (I.targetFam V1', I.targetFam V) then
	       let 
		 val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	       in
		 ltLF (G, Q, TG, PG, ((U', I.Dot (I.Exp (X), s1')), 
				      (V', I.Dot (I.Exp (X), s2'))),
		       UsVs, P, sc)
	       end
	     else true (* possibly redundant if lhs always subordinate to rhs *))
      | ltLFW (G, Q, TG, PG, UsVs, UsVs', P, sc) =
	     (* optimized - orig. activeL *)
          focusL (G, Q, I.Decl(TG, Less (R.Arg UsVs, R.Arg UsVs')), PG, P, sc)

    (* invariant: UsVs' is AtomicNotp *)
    and leLF (G, Q, TG, PG, UsVs, UsVs', P, sc) = 
	leLFW (G, Q, TG, PG, Whnf.whnfEta UsVs, UsVs', P, sc)
    and leLFW (G, Q, TG, PG, 
	       UsVs' as ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
		(I.Pi ((I.Dec (_, V2'), _), V'), s2')), UsVs as (Us,(V,s)), P, sc) = 
	  (if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	     let  (* enforce that X is only instantiated to parameters *) 
	       val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	       val sc' = fn () => (isParameter (Q, X); sc ())    
	     in
	       leLF (G, Q, TG, PG, ((U', I.Dot (I.Exp (X), s1')), 
				     (V', I.Dot (I.Exp (X), s2'))),
		     UsVs, P, sc')
	    (*    -bp8/7/00. dead code
	     orelse 
	       (activeL (G, Q, TG, PG, I.Decl(I.Null, Less (R.Arg UsVs', R.Arg UsVs)), P, sc)
		andalso  
		activeL (G, Q, TG, PG, I.Decl(I.Null, Eq (R.Arg UsVs', R.Arg UsVs)), P, sc)) *)
	     end
	   else
	     if Subordinate.below (I.targetFam V1', I.targetFam V) then
	       let 
		 val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	       in
		 leLF (G, Q, TG, PG, ((U', I.Dot (I.Exp (X), s1')), 
				      (V', I.Dot (I.Exp (X), s2'))),
		       UsVs, P, sc)
	       end
	     else true (* possibly redundant if lhs always subordinate to rhs *))
      | leLFW (G, Q, TG, PG, UsVs, UsVs', P, sc) =
        (* optimized - orig. activeL *)
          (focusL (G, Q, I.Decl(TG, Less (R.Arg UsVs, R.Arg UsVs')), PG, P, sc)
	   andalso  
	   focusL (G, Q, I.Decl(TG, Eq (R.Arg UsVs, R.Arg UsVs')), PG, P, sc))

    and eqLF (G, Q, TG, PG, UsVs, UsVs', P, sc) = 
	eqLFW (G, Q, TG, PG, Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P, sc)
    and eqLFW (G, Q, TG, PG, 
	       ((I.Lam (D as I.Dec (_, V1'), U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
	       ((I.Lam (D' as I.Dec (_, V1''), U''), s1''), (I.Pi ((I.Dec (_, V2''), _), V''), s2'')),
	       P, sc) = 
	  let
	    val (G', Q') = (I.Decl (G, N.decLUName (G, I.decSub (D, s1'))),
			    I.Decl (Q, Universal))
	    val X = I.newEVar (G', I.EClo (V1'', s1'')) (* = I.newEVar (I.EClo (V2', s2')) *)	   
	  in
	    eqLF (G', Q', TG, PG, ((U', I.Dot (I.Exp(X), s1')),  (V', I.Dot(I.Exp(X), s2'))), 
		  ((U'', I.Dot (I.Exp(X), s1'')), 
		   (V'', I.Dot (I.Exp(X), s2''))), P, 
		  fn () => (isParameter (Q', X); sc ()))
	   end 
       | eqLFW (G, Q, TG, PG, UsVs, UsVs', P, sc) = 
	   activeL (G, Q, TG, PG, I.Decl(I.Null, Eq(R.Arg UsVs, R.Arg UsVs')), P, sc)
       
    (* focusL (G, Q, TG, PG, P, sc) = B *)
    and focusL (G, Q, TG, I.Null, P, sc) = 
          ((if (!Global.chatter) > 6 then  
	    print ("\n transition to focusT \n" ^ 
		   "focusT: " ^ fmtRGCtx(G, TG) ^
		   " L==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
          focusT (G, Q, TG, P, sc))
      | focusL (G, Q, TG, I.Decl(PG, Pi(D as I.Dec(_, V), P)), P', sc) = 
	let
(*	  val X = I.newEVar (G, I.EClo (V, I.id)) *)
	  val X = I.newEVar (G, V)
	  val sc' = fn () => (isParameter (Q, X); sc ())	      
	  val P1 = shiftP P (fn s => I.Dot (I.Exp(X),  s))
	in
	  (if (!Global.chatter) > 6 then  
	    (print ("\n instantiate Pi \n" );
	     print ( "focusT: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^
		   " L==>" ^  F.makestring_fmt (fmtPredicate(G, P')) ^"\n" );
	     print (" after " ^ fmtRGCtx(G, TG) ^ ", "  ^ fmtRGCtx(G, I.Decl(PG, P1))  ^
		    " L==>" ^  F.makestring_fmt (fmtPredicate(G, P')) ^"\n"))
	  else 
	    ());
	  focusL (G, Q, TG, I.Decl(PG, P1), P', sc')
	end 
      | focusL (G, Q, TG, I.Decl(PG, P' as Less(R.Arg UsVs, R.Arg (UsVs' as (Us', Vs')))), P, sc) = 
	  if isAtomic (G, Q, Us') then 
	    ltLF (G, Q, TG, PG, UsVs, UsVs', P, sc)
	  else 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Less(R.Lex O, R.Lex O')), P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Less(R.Simul O, R.Simul O')), P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Leq(R.Lex O, R.Lex O')), P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Leq(R.Simul O, R.Simul O')), P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Leq(R.Arg UsVs, R.Arg ((I.Lam (_, U'), s1'), (I.Pi ((D', _), V'), s2')))),
		P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Leq(R.Arg UsVs, R.Arg (UsVs' as ((I.Root (_, S), s), Vs)))), P, sc) = 
	    leLF (G, Q, TG, PG, UsVs, UsVs', P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as 
		Eq(R.Arg (UsVs as ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2))), 
		   R.Arg (UsVs' as ((I.Lam (_, U'), s1'), (I.Pi ((D', _), V'), s2'))))), P, sc) = 
	    eqLF (G, Q, TG, PG, UsVs, UsVs', P, sc)
      | focusL (G, Q, TG, I.Decl(PG, P' as Eq(R.Arg  ((I.Root (_, S), s), Vs), 
					      R.Arg ((I.Root (_, S'), s'), Vs'))), P, sc) = 
	    activeL (G, Q, TG, PG, I.Decl(I.Null, P'), P, sc)

   (* focusT (G, Q, TG, P, sc) = B *)
    and focusT (G, Q, TG, P as Eq(R.Arg UsVs', R.Arg UsVs), sc) = 
          focusTW (G, Q, TG, Eq(R.Arg (Whnf.whnfEta UsVs'), R.Arg (Whnf.whnfEta UsVs)), sc)
      | focusT (G, Q, TG, P as Less(R.Arg UsVs', R.Arg UsVs), sc) = 
          focusTW (G, Q, TG, Less(R.Arg UsVs', R.Arg (Whnf.whnfEta UsVs)), sc)
      | focusT (G, Q, TG, P, sc) = focusTW (G, Q, TG, P, sc)

    and focusTW (G, Q, TG, P as Eq(R.Arg (UsVs' as (Us', Vs')), R.Arg (UsVs as (Us, Vs))), sc) = 
        (if (isAtomic (G, Q, Us') orelse isAtomic (G, Q, Us)) then 	      
	   ((if (!Global.chatter) > 6 then  
	      print ("\n transition to focusT' \n" ^ 
		     "focusT': " ^ fmtRGCtx(G, TG) ^ 
		     " L==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
	  focusT' (G, Q, I.Null, TG, Eq(R.Arg UsVs', R.Arg UsVs), sc))
	 else 
	   ((if (!Global.chatter) > 6 then  
	       print ("\n not - atomic transition to focusR \n" ^ 
		      "focusR: " ^ fmtRGCtx(G, TG) ^ 
		      " R==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	     else 
	       ());
	   focusR(G, Q, TG, Eq(R.Arg UsVs', R.Arg UsVs), sc)))
      | focusTW (G, Q, TG, P as Less(R.Arg UsVs',  R.Arg (Us, Vs)), sc) = 
	  if isAtomic(G, Q, Us) then 
	    ((if (!Global.chatter) > 6 then  
	      print ("\n transition to focusT' \n" ^ 
		     "focusT': " ^ fmtRGCtx(G, TG) ^ 
		     " L==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
	    focusT' (G, Q, I.Null, TG, P, sc))
	  else 
	    ((if (!Global.chatter) > 6 then  
	      print ("\n transition to focusR \n" ^ 
		     "focusR: " ^ fmtRGCtx(G, TG) ^ 
		     " R==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
	  focusR (G, Q, TG, P, sc))

      | focusTW (G, Q, TG, P, sc) = 
	  ((if (!Global.chatter) > 6 then  
	      print ("\n transition to focusR \n" ^ 
		     "focusR: " ^ fmtRGCtx(G, TG) ^ 
		     " R==>" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
	  focusR (G, Q, TG, P, sc))

    (* focusT' (G, Q, TG, P, sc) = B 
       Invariant: P is atomic / max. unfolded. 
                  TG is atomic / max. unfoled
     *) 
    and focusT' (G, Q, TG', I.Null, Less(R.Arg UsVs, R.Arg UsVs'), sc) = 
         ((if (!Global.chatter) > 6 then  
	     print ("\n False " ^ fmtRGCtx(G, TG') ^ " T-->" 
		     ^  F.makestring_fmt (fmtPredicate(G, Less(R.Arg UsVs, R.Arg UsVs'))) ^"\n")
	   else 
	     ());
	   false)
        (* can be focusR *)
      | focusT' (G, Q, TG', I.Null, 
		  Eq(R.Arg UsVs1, R.Arg UsVs2), sc) =           
	  (conv (UsVs1, UsVs2)
	   orelse 
	   eq(G, Whnf.whnfEta UsVs1, Whnf.whnfEta UsVs2, sc))
      | focusT' (G, Q, TG', I.Decl(TG, Eq(R.Arg UsVs, R.Arg UsVs')), 
		  Eq(R.Arg UsVs1 , R.Arg UsVs2), sc) =                     
	  (conv (UsVs1, UsVs2)
	   orelse 
	   eq(G, Whnf.whnfEta UsVs1, Whnf.whnfEta UsVs2, sc)
	   orelse	   
	   transEqW (G, Q, union(TG',TG), UsVs, UsVs', 
		     Eq(R.Arg UsVs1 , R.Arg UsVs2), sc)
	   orelse 
	   focusT' (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), TG, 
		    Eq(R.Arg UsVs1 , R.Arg UsVs2), sc))

      | focusT' (G, Q, TG', I.Decl(TG, Less(R.Arg UsVs, R.Arg UsVs')), 
		  Eq(R.Arg UsVs1 , R.Arg UsVs2), sc) =           
	  focusT' (G, Q, I.Decl(TG', Less(R.Arg UsVs, R.Arg UsVs')), TG, 
		   Eq(R.Arg UsVs1 , R.Arg UsVs2), sc)
      (* less *)
      | focusT' (G, Q, TG', I.Decl(TG, Eq(R.Arg UsVs, R.Arg UsVs')), 
		 Less(R.Arg UsVs1 , R.Arg UsVs2), sc) =  
	  (transEqW (G, Q, union(TG',TG), UsVs, UsVs', 
		     Less(R.Arg UsVs1 , R.Arg UsVs2), sc)
	   orelse 
	   focusT' (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), TG, 
		    Less(R.Arg UsVs1 , R.Arg UsVs2), sc))

      | focusT' (G, Q, TG', I.Decl(TG, Less(R.Arg UsVs, R.Arg UsVs')), 
		 Less(R.Arg UsVs1 , R.Arg UsVs2), sc) =  
	  (transLtW (G, Q, union(TG',TG), UsVs, UsVs',
		     Less(R.Arg UsVs1 , R.Arg UsVs2), sc)
	   orelse 
	   focusT' (G, Q, I.Decl(TG', Less(R.Arg UsVs, R.Arg UsVs')), TG, 
		    Less(R.Arg UsVs1 , R.Arg UsVs2), sc))

    and transEqW (G, Q, TG, UsVs, UsVs', Eq(R.Arg UsVs1 , R.Arg UsVs2), sc) = 
          ((eq (G, Whnf.whnfEta UsVs, UsVs1, sc) andalso            (* id *)
	    eq (G, Whnf.whnfEta UsVs', UsVs2, sc))
	   orelse 
	   (eq (G, Whnf.whnfEta UsVs', UsVs1, sc) andalso              (* id-sym *)
	    (eq (G, Whnf.whnfEta UsVs, UsVs2, sc)))
	   orelse 
	   (eq (G, Whnf.whnfEta UsVs, UsVs2, sc) andalso               (* t1 *)
	    activeR (G, Q, TG, I.Null, Eq(R.Arg UsVs1 , R.Arg UsVs'), sc))
	   orelse 
	   ((eq (G, Whnf.whnfEta UsVs', UsVs2, sc) andalso              (* t2 *)
	     activeR (G, Q, TG, I.Null, Eq(R.Arg UsVs1 , R.Arg UsVs), sc))))
      | transEqW (G, Q, TG, UsVs, UsVs', Less(R.Arg UsVs1 , R.Arg UsVs2), sc) = 
	    ((eq (G, Whnf.whnfEta UsVs, UsVs2, sc) andalso           (* t1 *)
	     focusR (G, Q, TG, Less(R.Arg UsVs1 , R.Arg UsVs'), sc))	    
	    orelse 
	    (eq (G, Whnf.whnfEta UsVs', UsVs2, sc) andalso              (* t2 *)
	     focusR (G, Q, TG, Less(R.Arg UsVs1 , R.Arg UsVs), sc)))

    and transLtW (G, Q, TG, UsVs, UsVs', Less(R.Arg UsVs1 , R.Arg UsVs2), sc) = 
	  ((eq (G, Whnf.whnfEta UsVs, UsVs1, sc) andalso            (* id *)
	    eq (G, UsVs', Whnf.whnfEta UsVs2, sc))
	   orelse 
	   (eq (G, Whnf.whnfEta UsVs', UsVs2, sc) andalso
	    focusR (G, Q, TG, Less(R.Arg UsVs1, R.Arg UsVs), sc))
	   orelse
	   (eq (G, Whnf.whnfEta UsVs', UsVs2, sc) andalso
	    activeR (G, Q, TG, I.Null, Eq(R.Arg UsVs1, R.Arg UsVs), sc)))
	   

   and ltLexLA (G, Q, TG, PG, AG, [], [], P, sc) = 
         true
(* bp Mon Aug  7 08:48:07 2000	activeL (G, Q, TG, PG, AG, P, sc)*)
     | ltLexLA (G, Q, TG, PG, AG,(O::Olist), (O'::O'list), P, sc) = 
	activeL (G, Q, TG, PG, I.Decl(AG, Less(O, O')), P, sc)
	andalso 
	ltLexLA (G, Q, TG, PG, I.Decl(AG, Eq(O, O')), Olist, O'list, P, sc)

   and ltSimulLA  (G, Q, TG, PG, AG, [], [], P, sc) = 
         activeL (G, Q, TG, PG, AG, P, sc)  (* should not happen *)
     | ltSimulLA (G, Q, TG, PG, AG, [O], [O'], P, sc) =   (* base case *)
	 activeL (G, Q, TG, PG, I.Decl(AG, Less(O, O')), P, sc)
	 
     | ltSimulLA (G, Q, TG, PG, AG, (O::Olist), (O'::O'list), P, sc) = 
	 activeL (G, Q, TG, PG, I.Decl(I.Decl(AG, Less(O, O')), Leq(R.Simul Olist, R.Simul O'list)),
		 P, sc)
	andalso 
	ltSimulLA (G, Q, TG, PG, I.Decl(AG, Eq(O, O')), Olist, O'list, P, sc)

   and eqLexLA (G, Q, TG, PG, AG, [], [], P, sc) = 
	activeL (G, Q, TG, PG, AG, P, sc)
      | eqLexLA (G, Q, TG, PG, AG,(O::Olist), (O'::O'list), P, sc) = 
	eqLexLA (G, Q, TG, PG, I.Decl(AG, Eq(O, O')), Olist, O'list, P, sc)
   and eqSimulLA (G, Q, TG, PG, AG, [], [], P, sc) = 
	activeL (G, Q, TG, PG, AG, P, sc)
      | eqSimulLA (G, Q, TG, PG, AG,(O::Olist), (O'::O'list), P, sc) = 
	eqSimulLA (G, Q, TG, PG, I.Decl(AG, Eq(O, O')), Olist, O'list, P, sc)

   and ltLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = 
         ltLAW (G, Q, TG, PG, AG, UsVs, Whnf.whnfEta UsVs', P, sc)
   and ltLAW (G, Q, TG, PG, AG, ((U,s1), (V, s2)),
	      ((I.Lam (_, U'), s1'), (I.Pi ((D, _), V'), s2')), P, sc) = 
	ltLA (I.Decl (G, N.decLUName (G, I.decSub (D, s2))), 
	      I.Decl (Q, Universal), shiftCtx TG (fn s => I.comp(s,I.shift)),
	       shiftCtx PG (fn s => I.comp(s,I.shift)),
	       shiftCtx AG (fn s => I.comp(s,I.shift)), 
	      ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift))), 
	      ((U', I.dot1 s1'), (V', I.dot1 s2')), 
	      shiftP P (fn s => I.comp(s, I.shift)), sc)
     | ltLAW (G, Q, TG, PG, AG, UsVs,
	      (Us' as (I.Root (I.Const c, S'), s'), Vs'), P, sc) = 
	(* note: ... M < c L--> P trivially true *)
	ltSpineLA (G, Q, TG, PG, AG, UsVs,((S', s'), (I.constType c, I.id)), P, sc) 
     | ltLAW (G, Q, TG, PG, AG, UsVs as ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), 
	      (Us' as (I.Root (I.BVar c, S'), s'), Vs'), P, sc) = 
	let 
	  val I.Dec (_, V') = I.ctxDec (G, c)
	in
	  if isAtomic(G, Q, (I.Root (I.BVar c, S'), s')) then (* atomic term not a param. *)
	    activeL (G, Q, TG, I.Decl(PG, Less(R.Arg UsVs, R.Arg (Us', Vs'))), AG, P, sc)
	  else 
	    ltSpineLA (G, Q, TG, PG, AG, UsVs, ((S', s'), (V', I.id)), P, sc)
	end 

     | ltLAW (G, Q, TG, PG, AG, UsVs as ((I.Root (_, S), s), Vs), 
	      (Us' as (I.Root (I.BVar c, S'), s'), Vs'), P, sc) = 
	let 
	  val I.Dec (_, V') = I.ctxDec (G, c)
	in
	  if isAtomic(G, Q, (I.Root (I.BVar c, S'), s')) then (* atomic term not a param. *)
	    activeL (G, Q, I.Decl(TG, Less(R.Arg UsVs, R.Arg (Us', Vs'))), PG, AG, P, sc)
	  else 
	    ltSpineLA (G, Q, TG, PG, AG, UsVs, ((S', s'), (V', I.id)), P, sc)
	end 


    (* ltSpineLA (G, Q, TG, PG, AG, UsVs, (Ss', Vs'), P, sc) *)
    and ltSpineLA (G, Q, TG, PG, AG, UsVs, (Ss', Vs'), P, sc) = 
	ltSpineLAW (G, Q, TG, PG, AG, UsVs, (Ss', Whnf.whnf Vs'), P, sc)
    and ltSpineLAW (G, Q, TG, PG, AG, UsVs, ((I.Nil, _), _), P, sc) = 
          true
      | ltSpineLAW (G, Q, TG, PG, AG, UsVs, ((I.SClo (S, s'), s''), Vs'), P, sc) =
	ltSpineLAW (G, Q, TG, PG, AG, UsVs, ((S, I.comp (s', s'')), Vs'), P, sc) 
      | ltSpineLAW (G, Q, TG, PG, AG, UsVs, 
		    ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), P, sc) = 
	(leLA (G, Q, TG, PG, AG, UsVs, ((U', s1'), (V1', s2')), P, sc)
	 andalso 
	 ltSpineLAW (G, Q, TG, PG, AG, UsVs, ((S', s1'),(V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
		    P, sc))
    (* leLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = B *) 

    and leLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = 
          leLAW (G, Q, TG, PG, AG, UsVs, Whnf.whnfEta UsVs', P, sc)
(*          leLAW (G, Q, TG, PG, AG, UsVs,  UsVs', P, sc) *)
    and leLAW (G, Q, TG, PG, AG, UsVs as ((U,s1), (V, s2)),
	      UsVs' as ((I.Lam (_, U'), s1'), (I.Pi ((D, _), V'), s2')), 
	       P, sc) = 
          let
	    val G' = I.Decl (G, N.decLUName (G, I.decSub (D, s2)))
	    val P' = shiftP P (fn s => (I.comp (s, I.shift)))
	  in 
	    leLA (I.Decl (G, N.decLUName (G, I.decSub (D, s2))), I.Decl (Q, Universal), 
		  shiftCtx TG (fn s => I.comp(s,I.shift)),
		  shiftCtx PG (fn s => I.comp(s,I.shift)),
		  shiftCtx AG (fn s => I.comp(s,I.shift)),
		  ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift))), 
		  ((U', I.dot1 s1'), (V', I.dot1 s2')), P' , sc)
	  end 
      | leLAW (G, Q, TG, PG, AG, UsVs as ((I.Root _, _), Vs), 
	      UsVs' as ((I.Root _, _), Vs'), P, sc) = 
	(ltLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) andalso 
	 eqLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc))
      | leLAW (G, Q, TG, PG, AG, UsVs as ((I.Lam (_, U'), s1'), _), 
	      UsVs' as ((I.Root _, _), Vs'), P, sc) = 
	  activeL (G, Q, TG, I.Decl(PG, Leq(R.Arg UsVs, R.Arg UsVs')), AG, P, sc)

   (*  eqLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = B *)
    and eqLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = 
          eqLAW (G, Q, TG, PG, AG, Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P, sc)
    and eqLAW (G, Q, TG, PG, AG, (UsVs as ((I.Lam _ , _), (I.Pi _, _))),
	      (UsVs' as ((I.Lam _, _), (I.Pi _, _))), P, sc) = 
	activeL (G, Q, TG, I.Decl(PG, Eq(R.Arg UsVs, R.Arg UsVs')), AG, P, sc)
      | eqLAW (G, Q, TG, PG, AG, ((I.Root (I.Const c, S'), s'), Vs),
	      ((I.Root (I.Const c1, S1'), s1'), Vs'), P, sc) = 
	if c = c1 then 	  
	  eqSpineLA (G, Q, TG, PG, AG, ((S', s'),(I.constType c, I.id)), 
		       ((S1', s1'),(I.constType c1, I.id)), P, sc)
	else 
	    (* trivially true *)
	    true
      | eqLAW (G, Q, TG, PG, AG, UsVs as ((I.Root (I.BVar c, S), s'), Vs),
	      UsVs' as ((I.Root (I.BVar c1, S1'), s1'), Vs'), P, sc) =  
	if AtomicNotP (G, Q, (I.Root (I.BVar c, S), s')) then 
	  (* substitute: TG[UsVs'] ~> TG[UsVs], PG[UsVs'] ~> PG[UsVs], AG[UsVs'] ~> AG[UsVs] *)
	  let
	    val TG' = substCtx (G, TG, I.BVar c, I.Root (I.BVar c1, S1'))
	    val PG' = substCtx (G, PG, I.BVar c, I.Root (I.BVar c1, S1'))
	    val AG' = substCtx (G, AG, I.BVar c, I.Root (I.BVar c1, S1'))
	    val _ = (if (!Global.chatter) > 6 then  
		       (print ("\n before subst \n" ^ 
			       "\n substitution " ^ F.makestring_fmt (fmtPredicate(G, Eq(R.Arg UsVs', R.Arg UsVs))) ^
			       "\n ActiveR: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^", " ^ fmtRGCtx(G, AG)^
			       " R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n");
			print ("\n after substition \n" ^ 
			       "\n ActiveR: " ^ fmtRGCtx(G, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs'))) ^ 
			       ", " ^ fmtRGCtx(G, PG') ^", " ^ fmtRGCtx(G, AG') ^" R-->" ^  
			       F.makestring_fmt (fmtPredicate(G, P)) ^"\n"))
		     else 
		       ())  
	  in 
	    activeL (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), PG', AG', P, sc)
	  end 
	else
	  (if AtomicNotP (G, Q, (I.Root (I.BVar c1, S1'), s1')) then   
	  (* substitute: TG[UsVs] ~> TG[UsVs'], PG[UsVs] ~> PG[UsVs'], AG[UsVs] ~> AG[UsVs'] *)
	     let
	       val TG' = substCtx (G, TG, I.BVar c1, I.Root (I.BVar c, S))
	       val PG' = substCtx (G, PG, I.BVar c1, I.Root (I.BVar c, S))
	       val AG' = substCtx (G, AG, I.BVar c1, I.Root (I.BVar c, S))
	       val _ = (if (!Global.chatter) > 6 then  
			  (print ("\n before subst \n" ^ 
				  "\n substitution " ^ F.makestring_fmt (fmtPredicate(G, Eq(R.Arg UsVs', R.Arg UsVs))) ^
				  "\n ActiveR: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^", " ^ fmtRGCtx(G, AG)^
				  " R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n");
			   print ("\n after substition \n" ^ 
				  "\n ActiveR: " ^ fmtRGCtx(G, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs'))) ^ 
				  ", " ^ fmtRGCtx(G, PG') ^", " ^ fmtRGCtx(G, AG') ^" R-->" ^  
				  F.makestring_fmt (fmtPredicate(G, P)) ^"\n"))
			else 
		       ())  
	     in 
	       activeL (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), PG', AG', P, sc)
	     end 
	   else  	    
	     let
	       val I.Dec (_, V') = I.ctxDec (G, c)
	       val I.Dec (_, V1') = I.ctxDec (G, c1)
	     in 
	       if c = c1 then 
		 eqSpineLA (G, Q, TG, PG, AG, ((S, s'),(V', I.id)), 
			    ((S1', s1'),(V1', I.id)), P, sc)
	       else 
	      (* trivially true *)
		 true
	     end) 

       | eqLAW (G, Q, TG, PG, AG, UsVs as ((I.Root (I.BVar c, S1), s'), Vs), 
		UsVs' as ((U', us'), Vs'), P, sc) = 
	  if AtomicNotP (G, Q, (I.Root (I.BVar c, S1), s')) then 
	    let
	      val TG' = substCtx (G, TG, I.BVar c, U')
	      val PG' = substCtx (G, PG, I.BVar c, U')
	      val AG' = substCtx (G, AG, I.BVar c, U')
	      val _ = (if (!Global.chatter) > 6 then  
			 (print ("\n before subst \n" ^ 
				"\n substitution " ^ F.makestring_fmt (fmtPredicate(G, Eq(R.Arg UsVs', R.Arg UsVs))) ^
				"\n ActiveR: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^", " ^ fmtRGCtx(G, AG)^
				" R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n");
			 print ("\n after substition \n" ^ 
				"\n ActiveR: " ^ fmtRGCtx(G, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs'))) ^ 
				", " ^ fmtRGCtx(G, PG') ^", " ^ fmtRGCtx(G, AG') ^" R-->" ^  
				F.makestring_fmt (fmtPredicate(G, P)) ^"\n"))
		       else 
			 ())

	    in 
	       activeL (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), PG', AG', P, sc)
	    end 
	  else 
	    true
      | eqLAW (G, Q, TG, PG, AG, UsVs' as ((U', us'), Vs'), 
	       UsVs as ((I.Root (I.BVar c, S1), s'), Vs), P, sc) = 
	  if AtomicNotP (G, Q, (I.Root (I.BVar c, S1), s')) then 
	    let
	      val TG' = substCtx (G, TG, I.BVar c, U') 
	      val PG' = substCtx (G, PG, I.BVar c, U')
	      val AG' = substCtx (G, AG, I.BVar c, U')
              val _ = (if (!Global.chatter) > 6 then  
			 (print ("\n before subst \n" ^ 
				"\n substitution " ^ F.makestring_fmt (fmtPredicate(G, Eq(R.Arg UsVs', R.Arg UsVs))) ^
				"\n ActiveR: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^", " ^ fmtRGCtx(G, AG) ^
				" R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n");
			 print ("\n after substition \n" ^ 
				"\n ActiveR: " ^ fmtRGCtx(G, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs'))) ^ 
				", " ^ fmtRGCtx(G, PG') ^", " ^ fmtRGCtx(G, AG') ^ 
				" R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n"))
		       else 
			 ())
	    in 
	      activeL (G, Q, I.Decl(TG', Eq(R.Arg UsVs, R.Arg UsVs')), PG', AG', P, sc)
	    end 
	  else 
	    true 
      | eqLAW (G, Q, TG, PG, AG, UsVs, UsVs', P, sc) = 
	  (print ("\n " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^", " ^ fmtRGCtx(G, AG) ^ 
		  " *** " ^ F.makestring_fmt (fmtPredicate(G, Eq(R.Arg UsVs, R.Arg UsVs'))) ^  
		  " *** " ^ 	" R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n");
	   (* true *)
	   activeL (G, Q, I.Decl(TG, Eq(R.Arg UsVs, R.Arg UsVs')), PG, AG, P, sc))
	     
							

    and eqSpineLA (G, Q, TG, PG, AG, (S as (Sp, _), s1), (S' as (Sp', _), s2), P, sc) = 
	eqSpineLAW (G, Q, TG, PG, AG, (S, Whnf.whnf s1), (S', Whnf.whnf s2), P, sc)
    and eqSpineLAW (G, Q, TG, PG, AG, ((I.Nil, s'), Vs'), ((I.Nil, s1'), V1s), P, sc) = 
	activeL (G, Q, TG, PG, AG, P, sc)
      | eqSpineLAW (G, Q, TG, PG, AG, ((I.SClo (S, s'), s''), Vs' as (V, s)), SVs, P, sc) = 
	eqSpineLA (G, Q, TG, PG, AG, ((S, I.comp (s', s'')), Vs'), SVs, P, sc)
      | eqSpineLAW (G, Q, TG, PG, AG, SVs, ((I.SClo (S, s'), s''), Vs' as (V, s)), P, sc) = 
	eqSpineLA (G, Q, TG, PG, AG, SVs, ((S, I.comp (s', s'')), Vs'), P, sc)
      | eqSpineLAW (G, Q, TG, PG, AG, 
		    ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
		    ((I.App (U'', S''), s1''), (I.Pi ((I.Dec (_, V1''), _), V2''), s2'')), 
		    P, sc) = 
	eqSpineLA (G, Q, TG, PG, 
		    I.Decl(AG, Eq(R.Arg ((U', s1'), (V1', s2')), 
				  R.Arg ((U'', s1''), (V1'', s2'')))),
		    ((S',s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), 
		    ((S'',s1''), (V2'', I.Dot (I.Exp (I.EClo (U'', s1'')), s2''))),
		    P, sc)
		    
    (* activeL (G, Q, TG, PG, AG, P, sc) = B *)
    and activeL (G, Q, TG, PG, I.Null, P, sc) = 
        ((if (!Global.chatter) > 6 then  
	    print ("\n transition to activeR \n" ^ 
		   "ActiveR: " ^ fmtRGCtx(G, TG) ^ ", " ^ fmtRGCtx(G, PG) ^
		   " R-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
	  activeR (G, Q, TG, PG, P, sc))
      (* Less *)
      | activeL (G, Q, TG, PG, I.Decl(AG, Less(R.Lex O, R.Lex O')), P, sc) = 
	ltLexLA (G, Q, TG, PG, AG, O, O', P, sc)
      | activeL (G, Q, TG, PG, I.Decl(AG, Less(R.Simul O, R.Simul O')), P, sc) = 
	ltSimulLA (G, Q, TG, PG, AG, O, O', P, sc)
      | activeL (G, Q, TG, PG, I.Decl(AG, Less(R.Arg UsVs, R.Arg UsVs')), P, sc) = 
	ltLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc)
      (* Leq *)
      | activeL (G, Q, TG, PG, I.Decl(AG, Leq(R.Lex O, R.Lex O')), P, sc) =
	activeL (G, Q, TG, PG, I.Decl(AG, Less(R.Lex O, R.Lex O')), P, sc)
	orelse 
	activeL (G, Q, TG, PG, I.Decl(AG, Eq(R.Lex O, R.Lex O')), P, sc)
      | activeL (G, Q, TG, PG, I.Decl(AG, Leq(R.Simul O, R.Simul O')), P, sc) =
	activeL (G, Q, TG, PG, I.Decl(AG, Less(R.Simul O, R.Simul O')), P, sc)
	orelse 
	activeL (G, Q, TG, PG, I.Decl(AG, Eq(R.Simul O, R.Simul O')), P, sc)
      | activeL (G, Q, TG, PG, I.Decl(AG, Leq(R.Arg UsVs, R.Arg UsVs')), P, sc) = 
	leLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc)
      (* Equal *)
      | activeL (G, Q, TG, PG, I.Decl(AG, Eq(R.Lex O, R.Lex O')), P, sc) = 
	eqLexLA (G, Q, TG, PG, AG, O, O', P, sc)
      | activeL (G, Q, TG, PG, I.Decl(AG, Eq(R.Simul O, R.Simul O')), P, sc) = 
	eqSimulLA (G, Q, TG, PG, AG, O, O', P, sc)
     | activeL (G, Q, TG, PG, I.Decl(AG, Eq(R.Arg UsVs, R.Arg UsVs')), P, sc) = 
	eqLA (G, Q, TG, PG, AG, UsVs, UsVs', P, sc)
     | activeL (G, Q, TG, PG, I.Decl(AG, Pi(D as I.Dec(_, V), P')), P, sc) = 
	activeL (G, Q, TG, I.Decl(PG, Pi(D, P')), AG, P, sc)
	
    fun deduce (G, Q, RG, P, sc) = 
      ((if (!Global.chatter) > 6 then  
	    print ("\n ActiveL: " ^ fmtRGCtx(G, RG) ^ 
		   " L-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ());
       let
	 val result = activeL (G, Q, I.Null, I.Null, RG, P, sc)
       in 
	 (if result then 
	   (if (!Global.chatter) > 6 then  
	    print ("\n SUCCESS : Deduce : " ^ fmtRGCtx(G, RG) ^ 
		   " L-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	  else 
	    ())
	 else 
	   (if (!Global.chatter) > 6 then  
	    print ("\n FAILS: " ^ fmtRGCtx(G, RG) ^ 
		   " L-->" ^  F.makestring_fmt (fmtPredicate(G, P)) ^"\n")
	    else 
	      ())); 
	    result
       end )

    (* closeCtx (G, RG, D) = RG''
       Invariant: 
            
            D is a declaration 
        and all P in RG: G, D |- P
         then G |- Pi x. P 
    *)
      
   fun closeCtx (G, RG, D) = 
         let 
	   fun orOrder (Less(R.Lex O, R.Lex O')) = true
	     | orOrder (Leq(R.Lex O, R.Lex O'))  = true 
	     | orOrder (Less(R.Simul O, R.Simul O')) = true 
	     | orOrder (Leq(O, O')) = true 
	     | orOrder _ = false
	   fun bind (I.Null, RG') = RG'
	     | bind (I.Decl(RG, P), RG') = 
		 ((if orOrder(P) then 
		     print ("\n WARNING: Quantified or-order " ^ 
			    F.makestring_fmt(fmtPredicate (G, Pi(D, P))) ^ 
			    " \n WARNING: reduction checker might be incomplete !!!!! \n ")
		   else 
		     ());
		   bind (RG, I.Decl(RG', Pi(D, P))))
	 in
	   bind (RG, I.Null)
	 end 
	
    (* checkGoal (G, Q, RG, (V, s), (V', s')) = RG'
     
       Invariant: 
       If   G : Q
       and  G |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
       then RG' = RG extended with reduction proposition derived from V
       else Error is raised.
    *)
    fun checkGoal (G, Q, RG, Vs, Vs', occ) = checkGoalW (G, Q, RG, Whnf.whnf Vs, Vs', occ)
    and checkGoalW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), (V', s'), occ) = 
        let
	  val _ = checkClause (G, Q, RG, (V1, s), P.label occ)
	in
	    checkGoal (I.Decl (G, N.decLUName(G, I.decSub (D, s))), 
		       I.Decl (Q, Universal), RG,   
		       (V2, I.dot1 s), 
		       (V', I.comp (s', I.shift)), P.body occ)
	end
      | checkGoalW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), (V', s'), occ) =
          checkGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
		     I.Decl (Q, Universal), RG, 
		     (V, I.dot1 s), 
		     (V', I.comp (s', I.shift)), P.body occ)
      | checkGoalW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), 
		    Vs' as (I.Root (I.Const a', S'), s'), occ) = 
	let
	  fun lookup (R.Empty, f) = R.Empty
	    | lookup (a's as R.LE (a, a's'), f) =
		if (f a) then a's else lookup (a's', f)
	    | lookup (a's as R.LT (a, a's'), f) =
		if (f a) then a's else lookup (a's', f)
	  val P = selectOcc (a, (S, s), occ)
	  val P' = selectOcc (a', (S', s'), occ) (* established invariant below *)
	  val a's = R.mutLookup a	(* should alway succeed *)
	  (* val _ = R.selLookup a' *)
	  (* check if a' terminates *)	  (* should always be true -fp *)
	  (* -bp reduction predicate *)
	  val RG' = ((if (!Global.chatter) > 5 then  
			 print ("\n reduction predicate " ^ 
				F.makestring_fmt (
				  fmtPredicate(G, selectROrder (a, (S, s)) ))^
				" added to context\n") 
			 else ()) 
		     ;   I.Decl(RG, selectROrder (a, (S, s))) ) 
               handle R.Error(msg) =>    
			(if (!Global.chatter) > 5 then  
			   (print ("\n no reduction predicate defined for "^
                                     I.conDecName (I.sgnLookup a));
                            RG ) 
			 else 
	                    RG)                     			     
	in
	  case lookup (a's, fn x' => x' = a') 
	    of R.Empty => RG' 
	     | R.LE _ =>  
	      (if deduce (G, Q, RG, Leq(P, P'), init) then 
		 (if (!Global.chatter) > 5 then  
		   (print  ("\n deduce  " ^ 
                            F.makestring_fmt (
                              fmtComparison (G, P, "<=", P')) ^ "\n");  
		    RG') 
		 else RG') 
	       else raise Error' (occ, "Termination violation:\n" 
				       ^ F.makestring_fmt (fmtComparison (G, P, "<=", P'))) 
		   ) 
	     | R.LT _ =>  
	      (if deduce (G, Q, RG, Less(P, P'), init) then   
		 (if (!Global.chatter) > 5 then  
		   (print  ("\n" ^ F.makestring_fmt (fmtComparison (G, P, "<", P')) ^ "\n"); 
		    RG') 
		 else RG') 
	       else raise Error' (occ, "Termination violation:\n" 
				       ^ F.makestring_fmt (fmtComparison (G, P, "<", P'))) 
		   ) 
	end 

    (* checkImp (G, Q, RG, (V1, s1), (V2, s2), occ) = RG'
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and RG is a context for derived reduction order assumptions 

       then RG' if V1[s1]  is "smaller" then  V2[s2]
    *)
    and checkImp (G, Q, RG, Vs, Vs', occ) = checkImpW (G, Q, RG, Vs, Whnf.whnf Vs', occ)

    and checkImpW (G, Q, RG, (V, s), (I.Pi ((D', I.No), V'), s'), occ) =
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		    I.Decl (Q, Existential), RG, 
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, RG, (V, s), (I.Pi ((D', I.Maybe), V'), s'), occ) =
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		    I.Decl (Q, Existential), RG, 
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, RG, Vs, Vs' as (I.Root (I.Const a, S), s), occ) = 
	  checkGoal (G, Q, RG, Vs, Vs', occ)

    (* checkClause (G, Q, RG, (V, s)) = RG''
     
       Invariant: 
       If   G : Q 
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  RG is a context of reduction propositions
       then if (V, s) satifies the termination condition in G 
               under possible assumptions in RG 
            then  return RG', a context for all the reduction assumptions
	    else exception Error is raised
    *)
    and checkClause (G, Q, RG, Vs, occ) = checkClauseW (G, Q, RG, Whnf.whnf Vs, occ)

    and checkClauseW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), occ) =
	  checkClause (I.Decl (G, N.decEName (G, I.decSub (D, s))), 
		       I.Decl (Q, Existential), RG, 
		       (V, I.dot1 s), P.body occ)
      | checkClauseW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
        let 
	  val RG' = checkClause (I.Decl (G, N.decEName (G, I.decSub (D, s))),
				 I.Decl (Q, Existential), RG, 
				 (V2, I.dot1 s), P.body occ)
	in 
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D, s))),
		    I.Decl (Q, Existential), RG', (V1, I.comp (s, I.shift)), 
		    (V2, I.dot1 s), P.label occ)
	end
      |      checkClauseW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), occ) = RG



    (* checkRImp (G, Q, RG, RG', (V1, s1), occ) = RG''
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and RG is a context of reduction propositions

       then RG' is RG extended with new reduction propositions which hold 
     *)

     fun checkRImp (G, Q, RG, RG', Vs, occ) = checkRImpW (G, Q, RG, RG', Whnf.whnf Vs, occ)

     and 
       
       checkRImpW (G, Q, RG, RG', Vs as (I.Root (I.Const a, S), s), occ) =
	(((if (!Global.chatter) > 5 then 
	    (print ("\n reduction predicate " ^ I.conDecName (I.sgnLookup a) ^ " red. order added");
	    print ("\n reduction predicate is " ^ (F.makestring_fmt (fmtPredicate(G, selectROrder (a, (S, s))))) ^ "\n"))
	  else ());
	    I.Decl(RG', selectROrder (a, (S, s))))
	     handle R.Error(s) => 
	       (if (!Global.chatter) > 5 then 
		  (print ("\n no reduction predicate defined for " ^ I.conDecName (I.sgnLookup a));RG )
		else
		  RG'))
	    
       | checkRImpW (G, Q, RG, RG', (I.Pi ((D, I.Maybe), V), s), occ) = 
	    let 
	      val RG'' = checkRImp (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
				    I.Decl (Q, Universal), RG, RG', (V, I.dot1 s), P.body occ)
	      val _ = if (!Global.chatter) > 5 then 
		        (print ("\n close ctx "))
		      else
			()
	    in 
	      closeCtx (G, RG'', D)
	    end 
	        
       | checkRImpW (G, Q, RG, RG', (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) = 
	    (checkReduction (I.Decl(G,N.decLUName (G, I.decSub (D, s))), I.Decl(Q, Universal),
			      union(RG, RG'), (V1, I.comp(s, I.shift)), P.label occ);
	     let
	       val RG'' = checkRImp (I.Decl (G, N.decLUName (G, I.decSub (D, s))),
				     I.Decl (Q, Universal), RG, RG',  
				     (V2, I.dot1 s), P.body occ)   
	       val I.Decl(_, P'') = RG''
	       val _ = if (!Global.chatter) > 5 then 
		          (print ("\n  G, D |- ");
			   print (F.makestring_fmt (fmtPredicate(I.Decl (G, N.decLUName (G, I.decSub (D, s))), P''))))
		       else
			 ()
	     in
	       closeCtx(G, RG'', D)
	     end) 

    (* checkReduction (G, Q, RG, (V, s)) = ()

       Invariant:
       If G: Q  
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  RG is a context of reduction propositions
       then V[s] satifies the reduction order
    *)

    and checkReduction (G, Q, RG, Vs, occ) = checkReductionW (G, Q, RG, Whnf.whnf Vs, occ)

    and checkReductionW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), occ) = 
	checkReduction (I.Decl (G, N.decEName (G, I.decSub (D, s))), 
			I.Decl (Q, Existential), RG, 
			(V, I.dot1 s), P.body occ)
      | checkReductionW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
	let 
	  val RG1 = checkRImp (G, Q, RG, I.Null, (V1,s), P.label occ)  
	  val RG2 = union (RG, RG1)
	  val RG3 = shiftCtx RG2 (fn us => I.comp(us, I.shift))
	in 
	  checkReduction (I.Decl (G, N.decEName (G, I.decSub (D, s))), 
			  I.Decl (Q, Existential), RG3,  
			  (V2, I.dot1 s), P.body occ)  
	end
      | checkReductionW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), occ) =
	let 
	  val RO = selectROrderOcc (a, (S, s), occ) 
	  val _ = if (!Global.chatter) > 5
		    then (print ("\n check reduction predicate ");
			  print (fmtRGCtx(G, RG) ^ " |- " ^  
				 (F.makestring_fmt (fmtPredicate(G, RO))) ^ " \n"))
		  else ()
	(* add mutual look up! - bp *)
	(* not needed; done automatically ...  -bp1/31/00.*)
	(* val RG' = I.Decl(RG, selectROrder (a, (S, s))) *)
	in
	  case RO
	    of Less(O, O') => 
	       if deduce(G, Q, RG, Less(O, O'), init) then 
		 if (!Global.chatter) > 5 then 
		     (print  ("\n" ^ F.makestring_fmt 
			      (fmtComparison (G, O, "<", O')) ^ "\n"))
		 else
		     ()
	       else  raise Error' (occ, "Reduction violation:\n" ^ F.makestring_fmt 
				   (fmtComparison (G, O, "<", O')))
	  | Leq(O, O') =>  
	     if deduce(G, Q, RG, Leq(O, O'), init) then 
	      if (!Global.chatter) > 5 then 
		  (print  ("\n" ^ F.makestring_fmt 
			   (fmtComparison (G, O, "<=", O')) ^ "\n"))
	      else
		  ()
	     else  raise Error' (occ, "Reduction violation:\n" ^ F.makestring_fmt 
				 (fmtComparison (G, O, "<=", O')))

           | Eq(O, O') =>  
	      if deduce (G, Q, RG, Eq(O, O'), init) then 
	        if (!Global.chatter) > 5 then 
		    (print  ("\n" ^ F.makestring_fmt 
			     (fmtComparison (G, O, "=", O')) ^ "\n"))
		else
		   ()
	     else  raise Error' (occ, "Reduction violation:\n" ^ F.makestring_fmt 
				 (fmtComparison (G, O, "=", O')))
	end


    (* checkFamReduction a = ()
       
       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate  
    *)
    fun checkFamReduction a =
	let 
	  fun checkFam' [] = ()
	    | checkFam' (I.Const b::bs) = 
		(if (!Global.chatter) > 4 then 
		   print ("[" ^ N.qidToString (N.constQid b) ^ ":")
		 else ();
		 (* reuse variable names when tracing *)
		 if (!Global.chatter) > 5 then N.varReset IntSyn.Null else ();
		 ((if (!Global.chatter) > 5 
		     then (* print ("\nTermination Check successful") *)
		       print ("\n Reduction Checking") 
		    else ());
		   ( (* checkClause (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top); *)
		    checkReduction (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top))
		    handle Error' (occ, msg) => error (b, occ, msg)
			 | R.Error (msg) => raise Error (msg));
		 if (!Global.chatter) > 4
		   then print ("]\n")
		 else ();
		 checkFam' bs)
	  val _ = if (!Global.chatter) > 4
		    then print "[Reduces: "
		  else ()
	in
	  (checkFam' (Index.lookup a);
	   if (!Global.chatter) > 4 then 
	     print "]\n" else ())
	end

    fun checkFam a =
	let 
	  fun checkFam' [] = ()
	    | checkFam' (I.Const b::bs) = 
		(if (!Global.chatter) > 4 then 
		   print ("[" ^ N.qidToString (N.constQid b) ^ ":")
		 else ();
		 (* reuse variable names when tracing *)
		 if (!Global.chatter) > 5 then N.varReset IntSyn.Null else ();
	        (checkClause (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top)
		 handle Error' (occ, msg) => error (b, occ, msg)
		      | Order.Error (msg) => raise Error (msg));
		 if (!Global.chatter) > 4
		   then print ("]\n")
		 else ();
		 checkFam' bs)
	  val _ = if (!Global.chatter) > 4
		    then print "[Terminates: "
		  else ()
	in
	  (checkFam' (Index.lookup a);
	   if (!Global.chatter) > 4 then 
	     print "]\n" else ())
	end

    fun reset () = (R.reset(); R.resetROrder())

  in
    val reset = reset 
    val checkFamReduction = checkFamReduction 
    val checkFam = checkFam  
  end (* local *)
end; (* functor Reduces  *)
