(* Termination checker *)
(* Author: Carsten Schuermann *)
(* See [Rohwedder,Pfenning ESOP'96] *)

functor Terminate (structure Global : GLOBAL
		   structure IntSyn': INTSYN
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn'
	           structure Conv : CONV
		     sharing Conv.IntSyn = IntSyn'
	           structure Unify : UNIFY
		     sharing Unify.IntSyn = IntSyn'
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
  :  TERMINATE =
struct
  structure IntSyn = IntSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths
    structure N = Names
    structure F = Formatter


    datatype Quantifier =                     (* Quantifier to mark parameters *)
      Universal                               (* Q ::= Uni                     *)
    | Existential                             (*     | Ex                      *)

    (* If Q marks all parameters in a context G we write   G : Q               *)

    exception Error' of P.occ * string

    fun error (c, occ, msg) =  
        (case Origins.originLookup c
	   of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) => 
	      raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
				       Origins.linesInfoLookup (fileName),
				       msg)))

    fun fmtOrder (G, O) =
        let
	  fun fmtOrder' (Order.Arg (Us, Vs)) =
	        F.Hbox [F.String "(", Print.formatExp (G, I.EClo Us),  F.String ")"]
	    | fmtOrder' (Order.Lex L) =
		F.Hbox [F.String "{", F.HOVbox0 1 0 1 (fmtOrders L), F.String "}"]
	    | fmtOrder' (Order.Simul L) =
		F.Hbox [F.String "[", F.HOVbox0 1 0 1 (fmtOrders L), F.String "]"]
	  
	  and fmtOrders nil = nil
	    | fmtOrders (O :: nil) = fmtOrder' O :: nil
	    | fmtOrders (O :: L) = fmtOrder' O :: F.Break :: fmtOrders L
	in
	  fmtOrder' O
	end

    fun fmtComparison (G, P, comp, P') =
        F.HOVbox0 1 0 1 [fmtOrder (G, P), F.Break, F.String comp, F.Break, fmtOrder (G, P')]

    (* select (a, (S, s)) = P
       
       Invariant:
       If   . |- a : V   G |- s : G'    G' |- S : V > type
       and  V = {x1:V1} ... {xn:Vn} type.
       then P = U1[s1] .. Un[sn] is parameter select of S[s] accoring to sel (a)
       and  G |- si : Gi  Gi |- Ui : Vi 
       and  G |- Vi[s]  == V[si] : type   forall 1<=i<=n
    *)
    fun select (a, (S, s)) =
        let 
	  val P = Order.selLookup a
	  val Vid = (I.constType a, I.id)
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
	  fun select' (Order.Arg n) = Order.Arg (select'' (n, ((S, s), Vid)))
	    | select' (Order.Lex L) = Order.Lex (map select' L)
	    | select' (Order.Simul L) = Order.Simul (map select' L)
	in
	  select' P
	end

    fun conv ((Us, Vs), (Us', Vs')) =
        Conv.conv (Vs, Vs') andalso  
	Conv.conv (Us, Us') 

    (* init () = true 

       Invariant:
       The inital constraint continuation
    *)
    fun init () = true

    fun isUniversal (Universal) = true
      | isUniversal (Existential) = false

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
    and isFreeEVar (I.EVar (_, _, _, ref nil), _) = true   (* constraints must be empty *)
      | isFreeEVar (I.Lam (D, U), s) = isFreeEVar (Whnf.whnf (U, I.dot1 s))
      | isFreeEVar _ = false

    (* For functions: lt, ltW, ltSpine, eq, le, leW *)
    (* first argument pair (UsVs) must be atomic! *)
    (* For all functions below: (UsVs) may not contain any EVars *)

    (* lt (G, Q, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2] 
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is a strict subterm of U'[s']
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U'[s'] contains EVars
    *)
    and lt (G, Q, UsVs, UsVs', sc) = 
          ltW (G, Q, UsVs, Whnf.whnfEta UsVs', sc)

    and ltW (G, Q, (Us, Vs), ((I.Root (I.Const c, S'), s'), Vs'), sc) = 
	  ltSpine (G, Q, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc)
      | ltW (G, Q, (Us, Vs), ((I.Root (I.BVar n, S'), s'), Vs'), sc) = 
	  let 
	    val I.Dec (_, V') = I.ctxDec (G, n)
	  in
	    ltSpine (G, Q, (Us, Vs), ((S', s'), (V', I.id)), sc)
	  end
      | ltW (G, Q, _, ((I.EVar _, _), _), _) = false
      | ltW (G, Q, ((U, s1), (V, s2)), 
	     ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	      (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc) =
          if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *) then 
	    let  (* enforce that X is only instantiated to parameters *) 
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      val sc' = fn () => (isParameter (Q, X); sc ())    
	    in
	      lt (G, Q, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc')
	    end
	  else
	    if Subordinate.below (I.targetFam V1', I.targetFam V) then
	      let 
		val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      in
		lt (G, Q, ((U, s1), (V, s2)), 
		    ((U', I.Dot (I.Exp (X), s1')), 
		     (V', I.Dot (I.Exp (X), s2'))), sc)
	      end
	    else false  (* possibly redundant if lhs always subordinate to rhs *)

    and ltSpine (G, Q, (Us, Vs), (Ss', Vs'), sc) = 
          ltSpineW (G, Q, (Us, Vs), (Ss', Whnf.whnf Vs'), sc) 

    and ltSpineW (G, Q, (Us, Vs), ((I.Nil, _), _), _) = false
      | ltSpineW (G, Q, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc) =
          ltSpineW (G, Q, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc)
      | ltSpineW (G, Q, (Us, Vs), ((I.App (U', S'), s1'), 
				   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc) = 
	  le (G, Q, (Us, Vs), ((U', s1'), (V1', s2')), sc) orelse 
	  ltSpine (G, Q, (Us, Vs), 
		   ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc)


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
    and eq (G, (Us, Vs), (Us', Vs'), sc) = 
        CSManager.trail (fn () =>
		           Unify.unifiable (G, Vs, Vs')
		           andalso Unify.unifiable (G, Us, Us')
		           andalso sc ())

    (* le (G, Q, ((U, s1), (V, s2)), (U', s'), sc) = B
     
       Invariant:
       B holds  iff  
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2] 
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is a equal to or a subterm of U'[s']
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] is atomic
       and only U'[s'] contains EVars
    *)
    and le (G, Q, UsVs, UsVs', sc) = eq (G, UsVs, UsVs', sc) orelse 
          leW (G, Q, UsVs, Whnf.whnfEta UsVs', sc)
    and leW (G, Q, ((U, s1), (V, s2)), 
	     ((I.Lam (D as I.Dec (_, V1'), U'), s1'), 
	      (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc) =
	if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *)
	  then 
	    let
	      val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      (* enforces that X can only bound to parameter or remain uninstantiated *)
	      val sc' = fn () => (isParameter (Q, X) andalso sc ())
	    in                         
	      le (G, Q, ((U, s1), (V, s2)), 
		  ((U', I.Dot (I.Exp (X), s1')), 
		   (V', I.Dot (I.Exp (X), s2'))), sc')
	    end
	else
	  if Subordinate.below  (I.targetFam V1', I.targetFam V)
	    then
	      let 
		val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
	      in
		le (G, Q, ((U, s1), (V, s2)), 
		    ((U', I.Dot (I.Exp (X), s1')), 
		     (V', I.Dot (I.Exp (X), s2'))), sc)
	      end
	  else false (* impossible, if additional invariant assumed (see ltW) *)
      | leW (G, Q, (Us, Vs), (Us', Vs'), sc) = 
	  lt (G, Q, (Us, Vs), (Us', Vs'), sc) 

    (* ltinit (G, Q, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B'

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2] 
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
    *)
    fun ltinit (G, Q, (Us, Vs), UsVs', sc) = 
          ltinitW (G, Q, Whnf.whnfEta (Us, Vs), UsVs', sc)

    and ltinitW (G, Q, (Us, Vs as (I.Root _, _)), UsVs', sc) =
          lt (G, Q, (Us, Vs), UsVs', sc)
      | ltinitW (G, Q, ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), 
		 ((U', s1'), (V', s2')), sc) =
          ltinit (I.Decl (G, N.decLUName (G, I.decSub (D, s2))),
		  I.Decl (Q, Universal), 
		  ((U, I.dot1 s1), (V, I.dot1 s2)), 
		  ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift))), sc)

    (* ordlt (G, Q, O1, O2) = B'
     
       Invariant:
       If   G : Q
       and  G |- O1 augmented subterms
       and  G |- O2 not contianing any EVars
       then B' holds iff O1 is smaller than O2 
    *)
    fun ordlt (G, Q, Order.Arg UsVs, Order.Arg UsVs') =  ltinit (G, Q, UsVs, UsVs', init)
      | ordlt (G, Q, Order.Lex L, Order.Lex L') = ordltLex (G, Q, L, L')
      | ordlt (G, Q, Order.Simul L, Order.Simul L') = ordltSimul (G, Q, L, L')

    (* ordltLex (G, Q, L1, L2) = B'
     
       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is lexically smaller than L2 
    *)
    and ordltLex (G, Q, nil, nil) = false
      | ordltLex (G, Q, O :: L, O' :: L') =
          ordlt (G, Q, O, O') 
	  orelse 
	  (ordeq (G, Q, O, O') andalso ordltLex (G, Q, L, L'))
      
    (* ordltSimul (G, Q, L1, L2) = B'
     
       Invariant:
       If   G : Q 
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously smaller than L2 
    *)
    and ordltSimul (G, Q, nil, nil) = false
      | ordltSimul (G, Q, O :: L, O' :: L') = 
          (ordlt (G, Q, O, O') andalso ordleSimul (G, Q, L, L'))
	  orelse 
	  (ordeq (G, Q, O, O') andalso ordltSimul (G, Q, L, L'))

    (* ordleSimul (G, Q, L1, L2) = B'
     
       Invariant:
       If   G : Q 
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously less than or equal to L2 
    *)
    and ordleSimul (G, Q, nil, nil) = true
      | ordleSimul (G, Q, O :: L, O' :: L') =
          ordle (G, Q, O, O') andalso ordleSimul (G, Q, L, L') 

    (* ordeq (G, Q,  O1, O2) = B'
     
       Invariant:
       If   G : Q 
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not contianing any EVars
       then B' holds iff O1 is convertible to O2 
    *)
    and ordeq (G, Q, Order.Arg UsVs, Order.Arg UsVs') =  conv (UsVs, UsVs')
      | ordeq (G, Q, Order.Lex L, Order.Lex L') = ordeqs (G, Q, L, L')
      | ordeq (G, Q, Order.Simul L, Order.Simul L') = ordeqs (G, Q, L, L')
      
    (* ordeqs (G, Q, L1, L2) = B'
     
       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is convertible to L2 
    *)
    and ordeqs (G, Q, nil, nil) = true
      | ordeqs (G, Q, O :: L, O' :: L') = 
          ordeq (G, Q, O, O') andalso ordeqs (G, Q, L, L')

    (* ordeq (G, Q, O1, O2) = B'
     
       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not contianing any EVars
       then B' holds iff O1 is convertible to O2 or O1 is smaller than O2 
    *)
    and ordle (G, Q, O, O') = 
          ordeq (G, Q, O, O') orelse ordlt (G, Q, O, O')

    (* checkGoal (G, Q, (V, s), (V', s')) = ()
     
       Invariant: 
       If   G : Q
       and  G |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
       then () 
       else Error is raised.
    *)
    fun checkGoal (G, Q, Vs, Vs', occ) = checkGoalW (G, Q, Whnf.whnf Vs, Vs', occ)
    and checkGoalW (G, Q, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), (V', s'), occ) = 
          (checkClause (G, Q, (V1, s), P.label occ); 
	   checkGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
		      I.Decl (Q, Universal), 
		      (V2, I.dot1 s), 
		      (V', I.comp (s', I.shift)), P.body occ))
      | checkGoalW (G, Q, (I.Pi ((D, I.Maybe), V), s), (V', s'), occ) =
          checkGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
		     I.Decl (Q, Universal),
		     (V, I.dot1 s), 
		     (V', I.comp (s', I.shift)), P.body occ)
      | checkGoalW (G, Q, Vs as (I.Root (I.Const a, S), s), 
		    Vs' as (I.Root (I.Const a', S'), s'), occ) = 
	let
	  fun lookup (Order.Empty, f) = Order.Empty
	    | lookup (a's as Order.LE (a, a's'), f) =
		if (f a) then a's else lookup (a's', f)
	    | lookup (a's as Order.LT (a, a's'), f) =
		if (f a) then a's else lookup (a's', f)
	  val P = select (a, (S, s))	(* only if a terminates? *)
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ N.constName a)
	  val P' = select (a', (S', s')) (* only if a' terminates? *)
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ N.constName a')
	  val a's = Order.mutLookup a	(* always succeeds? -fp *)
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ N.constName a)
	  val _ = Order.selLookup a'	(* check if a' terminates --- should always succeed? -fp *)
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ N.constName a)
	in
	  case lookup (a's, fn x' => x' = a')
	    of Order.Empty => ()
	     | Order.LE _ => 
	       if ordle (G, Q, P, P') then
		 if (!Global.chatter) >= 5 then 
		   print  ("\n" ^ F.makestring_fmt (fmtComparison (G, P, "<=", P')) ^ "\n")
		 else ()
	       else raise Error' (occ, "Termination violation:\n"
				       ^ F.makestring_fmt (fmtComparison (G, P, "<=", P')))
	     | Order.LT _ => 
	       if ordlt (G, Q, P, P') then  
		 if (!Global.chatter) >= 5 then 
		   print  ("\n" ^ F.makestring_fmt (fmtComparison (G, P, "<", P')) ^ "\n")
		 else ()
	       else raise Error' (occ, "Termination violation:\n"
				       ^ F.makestring_fmt (fmtComparison (G, P, "<", P')))
	end

    (* checkImp (G, Q, (V1, s1), (V2, s2), occ) = ()
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration

       then () if V1[s1]  is "smaller" then  V2[s2]
    *)
    and checkImp (G, Q, Vs, Vs', occ) = checkImpW (G, Q, Vs, Whnf.whnf Vs', occ)

    and checkImpW (G, Q, (V, s), (I.Pi ((D', I.No), V'), s'), occ) =
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		    I.Decl (Q, Existential),
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, (V, s), (I.Pi ((D', I.Maybe), V'), s'), occ) =
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		    I.Decl (Q, Existential),
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, Vs, Vs' as (I.Root (I.Const a, S), s), occ) = 
	  checkGoal (G, Q, Vs, Vs', occ)

    (* checkClause (G, Q, (V, s)) = ()
     
       Invariant: 
       If   G : Q
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       then if (V, s) satifies the termination condition in G then  ()
	 else exception Error is raised
    *)
    and checkClause (G, Q, Vs, occ) = checkClauseW (G, Q, Whnf.whnf Vs, occ)

    and checkClauseW (G, Q, (I.Pi ((D, I.Maybe), V), s), occ) =
	  checkClause (I.Decl (G, N.decEName (G, I.decSub (D, s))), 
		       I.Decl (Q, Existential), 
		       (V, I.dot1 s), P.body occ)
      | checkClauseW (G, Q, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
          (checkImp (I.Decl (G, N.decEName (G, I.decSub (D, s))),
		     I.Decl (Q, Existential),
		     (V1, I.comp (s, I.shift)), (V2, I.dot1 s), P.label occ);
	   checkClause (I.Decl (G, N.decEName (G, I.decSub (D, s))),
			I.Decl (Q, Existential), 
			(V2, I.dot1 s), P.body occ))
      | checkClauseW (G, Q, Vs, occ) = ()

	  
    (* checkFam a = ()
       
       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate  
    *)
    fun checkFam a =
	let 
	  fun checkFam' nil = ()
	    | checkFam' (I.Const b::bs) = 
		(if (!Global.chatter) >= 4 then 
		   print ("[" ^ N.constName b ^ ":")
		 else ();
		 (* reuse variable names when tracing *)
		 if (!Global.chatter) >= 5 then N.varReset () else ();
		 (checkClause (I.Null, I.Null, (I.constType (b), I.id), P.top)
		   handle Error' (occ, msg) => error (b, occ, msg)
			| Order.Error (msg) => (print "!!!\n"; raise Error (msg)));
		 if (!Global.chatter) >= 4
		   then print ("]\n")
		 else ();
		 checkFam' bs)
	  val _ = if (!Global.chatter) >= 4
		    then print "[Terminates: "
		  else ()
	in
	  (checkFam' (Index.lookup a);
	   if (!Global.chatter) >= 4 then 
	     print "]\n" else ())
	end
  in
    val reset = Order.reset
    val check = fn Vs => checkClause (I.Null, I.Null, Vs, P.top)
    val checkFam = checkFam
  end (* local *)
end; (* functor Terminate *)
