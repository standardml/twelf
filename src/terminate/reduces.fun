(* Reduction and Termination checker *)
(* an extended version of the file termintes.fun  *)
(* Author: Carsten Schuerman  *)
(* Modified: Brigitte Pientka *)
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
		raise Error (P.wrapLoc (P.Loc (fileName, P.occToRegionDec occDec occ), msg)))

   fun union (I.Null, G) = G
     | union (G, I.Null) = G
     | union (G, I.Decl(G', P)) = 
         union (I.Decl(G, P), G')

   (* shiftO f O = O'
    if O is an order 
      then we shift the substitutions which are associated
	with its terms by applying f to it
    *)

    fun shiftO (R.Arg ((U,us), (V,vs))) f = 
		 R.Arg ((U, (f us)), (V, (f vs)))
      | shiftO (R.Lex L) f = R.Lex (map (fn O => shiftO O f) L)
      | shiftO (R.Simul L) f = R.Simul (map (fn O => shiftO O f) L)

    fun shiftP (Less(O1, O2)) f = Less(shiftO O1 f, shiftO O2 f)
      | shiftP (Leq(O1, O2)) f = Leq(shiftO O1 f, shiftO O2 f)
      | shiftP (Eq(O1, O2)) f = Eq(shiftO O1 f, shiftO O2 f)
      | shiftP (Pi(D, P)) f = Pi(D, shiftP P f)      

    fun shiftCtx I.Null f = I.Null
      | shiftCtx (I.Decl(G, P)) f =
	  I.Decl(shiftCtx G f, shiftP P f)
	
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


    fun fmtOrder (G, O) =
        let
	  fun fmtOrder' (R.Arg (Us as (U, s), Vs)) =
	        F.Hbox [F.String "(", Print.formatExp (G, I.EClo Us), F.String ")"]
	    | fmtOrder' (R.Lex L) =
		F.Hbox [F.String "{", F.HOVbox0 1 0 1 (fmtOrders L), F.String "}"]
	    | fmtOrder' (R.Simul L) =
		F.Hbox [F.String "[", F.HOVbox0 1 0 1 (fmtOrders L), F.String "]"]
	  
	  and fmtOrders nil = nil
	    | fmtOrders (O :: nil) = fmtOrder' O :: nil
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
    and isFreeEVar (I.EVar (_, _, _,ref nil), _) = true   (* constraints must be empty *)
      | isFreeEVar (I.Lam (D, U), s) = isFreeEVar (Whnf.whnf (U, I.dot1 s))
      | isFreeEVar _ = false

    (* For functions: lt, LtW, LtSpine, eq, le, leW *)
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
	ltW (G, Q, UsVs,Whnf.whnfEta UsVs' , sc)

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
    and le (G, Q, UsVs, UsVs', sc) = 
	eq (G, UsVs, UsVs', sc)
	orelse 
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
	  else false  (* impossible, if additional invariant assumed (see ltW) *)
      | leW (G, Q, (Us, Vs), (Us', Vs'), sc) = 
	  lt (G, Q, (Us, Vs), (Us', Vs'), sc) 
	      

    (* -bp *)

    (* deriveEq (G, Q, RG, RG', Rpi, ((U, s), (V, s')), ((U1, s1), (V1, s1')), sc) = B
     
     Invariant:
     B holds iff
           G : Q
       and G |- s : G''     G'' |- U : V'
       and G |- s' : G'     G'  |- V : L
       and G |- U[s] : V[s']
       and G |- s1 : G3     G3 |- U1 : V1'
       and G |- s1': G4     G4 |- V1 : L'
       and G |- RG and G |- RG' and G |- Rpi
       and RG subset of RG',	 
       and RG |- U[s] = U1[s1] 
       and RG', Rpi |- U[s] = U1[s1] 
       and sc is a constraint continuation representing restrictions on EVars
     
    *)
  
    and deriveEq (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc) = 
	let
	  val (Us, Vs) =  Whnf.whnfEta UsVs
	in
	    eq (G, UsVs, U1sV1s, sc) 
	  orelse  
	    deriveEq' (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc)
	  orelse
	   (let val _ = (if (!Global.chatter) >= 5 then 
			  print ("\n deriveEqSbt " ^ fmtRGCtx(G, RG) ^ " |- " ^  
				 F.makestring_fmt (
				  fmtPredicate(G, Eq(R.Arg UsVs, R.Arg U1sV1s)))
				 ^"\n")
			else 
			  ())
	    in 
	      deriveEqSbt (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc)
	    end)
	end

    and deriveEqSbt (G, Q, RG, RG', Rpi, UsVs, UsVs', sc) = 
        let 
	  val (Us, Vs) = Whnf.whnfEta UsVs 
	  val (Us', Vs') = Whnf.whnfEta UsVs'
	  val _ = (if (!Global.chatter) >= 5 then 
		     print ("\n deriveEqSbt " ^ fmtRGCtx(G, RG) ^ " |- " ^  
			    F.makestring_fmt(fmtPredicate(G, Eq(R.Arg UsVs, R.Arg UsVs'))) ^"\n")
		   else 
		     ())
	in 
	  case (Us, Us') of
	    ((I.Root (I.Const c, S'), s'), (I.Root (I.Const c1, S1'), s1')) => 
	      if c = c1 then 
		((if (!Global.chatter) >= 5 then 
		    (print ("heads are const. and they are equal \n");
		     print ("\n derive " ^ 
			    F.makestring_fmt 
			    (fmtPredicate(G, Eq(R.Arg (Us, Vs), R.Arg (Us', Vs')))) ^"\n"))
		  else 
		    ());
		  deriveEqSpine (G, Q, RG, RG', Rpi, 
				 ((S', s'),(I.constType c, I.id)), 
				 ((S1', s1'),(I.constType c1, I.id)), sc))
	      else 
		false
	      | ((I.Root (I.BVar c, S'), s'),(I.Root (I.BVar c1, S1'), s1')) => 
		let 
		  val I.Dec (_, V') = I.ctxDec (G, c)
		  val I.Dec (_, V1') = I.ctxDec (G, c1)
		  val _ =  (if (!Global.chatter) >= 5 then 
			      print ("heads are bound vars. \n")
			    else 
			      ())
		in
		  (c = c1) andalso 
		  deriveEqSpine (G, Q, RG, RG', Rpi,((S', s'), (V', I.id)), ((S1', s1'), (V1', I.id)), sc)
		end 
	      | ((I.Lam (D as I.Dec (_, V1'), U'), s1'), (I.Lam (D' as I.Dec (_, V1''), U''), s1'')) => 
		let
		  val (I.Pi ((I.Dec (_, V2'), _), V'), s2') = Vs
		  val (I.Pi ((I.Dec (_, V2''), _), V''), s2'') = Vs'
		  val (G', Q') = (I.Decl (G, N.decLUName (G, I.decSub (D, s1'))),
				  I.Decl (Q, Universal))
		  val X = I.newEVar (G', I.EClo (V1'', s1'')) (* = I.newEVar (I.EClo (V2', s2')) *)
		  val sc' = fn () => (isParameter (Q', X); sc ())    
		  val newUsVs = ((U', I.dot1 s1'), (V', I.dot1 s2'))
		  val newUsVs' = ((U'', I.Dot (I.Exp(X), I.comp(s1'', I.shift))), 
				  (V'', I.Dot (I.Exp(X), I.comp(s2'', I.shift))))
		  val _ = (if (!Global.chatter) >= 5 then 
			     print ("\n to show deriveEqSbt lam case: " ^ fmtRGCtx(G, Rpi) ^ " |- " ^  
				    (F.makestring_fmt
				     (fmtPredicate(G', Eq (R.Arg newUsVs, R.Arg newUsVs')))))
			   else 
			     ())
		in
		  focusPi (G', Q', RG', Rpi, Eq (R.Arg newUsVs, R.Arg newUsVs'), sc') 
		end 
  	      | _ => false
	end 
    and deriveEqSpine(G, Q, RG, RG', Rpi, (Us, Vs), (U1s, V1s1), sc) = 
          deriveEqSpineW (G, Q, RG, RG', Rpi, (Us, (Whnf.whnf Vs)), (U1s, Whnf.whnf V1s1), sc)

    and deriveEqSpineW (G, Q, RG, RG', Rpi, ((I.Nil, s'), Vs'), ((I.Nil, s1'), V1s), sc) = sc()
      | deriveEqSpineW (G, Q, RG, RG', Rpi, ((I.SClo (S, s'), s''), Vs' as (V, s)), SV1s, sc) = 
          deriveEqSpine (G, Q, RG, RG', Rpi, ((S, I.comp (s', s'')), Vs'), SV1s, sc)

      | deriveEqSpineW (G, Q, RG, RG', Rpi, SVs, ((I.SClo (S, s'), s''), Vs' as (V, s)), sc) = 
	   deriveEqSpine (G, Q, RG, RG', Rpi, SVs, ((S, I.comp (s', s'')), Vs'), sc)

       | deriveEqSpineW (G, Q, RG, RG', Rpi, ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')),
			((I.App (U'', S''), s1''), (I.Pi ((I.Dec (_, V1''), _), V2''), s2'')), sc)= 
	   deriveEq (G, Q, RG, RG', Rpi, ((U', s1'), (V1', s2')), ((U'', s1''), (V1'', s2'')), sc)
	   andalso
	   deriveEqSpine (G, Q, RG, RG', Rpi, ((S',s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))),
			 ((S'',s1''), (V2'', I.Dot (I.Exp (I.EClo (U'', s1'')), s2''))), sc)

      | deriveEqSpineW (G, Q, RG, RG', Rpi, _, _, sc) = (print "\n false " ; false)
      
      
    and	deriveEq' (G, Q, I.Null, RG', Rpi, UsVs, U1sV1s, sc) = false
      | deriveEq' (G, Q,
		  I.Decl(RG, Eq(R.Arg UsVs', R.Arg U1sV1s')), 
                  RG', Rpi, UsVs, U1sV1s, sc) = 
        let 
	  val _ = if (!Global.chatter) >= 5 then 
	              (print (" deriveEq' \n");
		       print (" ctx : " ^ fmtRGCtx (G, I.Decl(RG, Eq(R.Arg UsVs', R.Arg U1sV1s'))) 
			      ^ " |- " ^ F.makestring_fmt 
			      (fmtPredicate(G,Eq(R.Arg UsVs, R.Arg U1sV1s))) ^  "\n");
		       fmtDerive (G, Eq(R.Arg UsVs', R.Arg U1sV1s'),
				  Eq(R.Arg UsVs, R.Arg U1sV1s)))
		  else 
		    ()
	  val (Us',Vs') = Whnf.whnfEta UsVs'
	  val (U1s', V1s') = Whnf.whnfEta U1sV1s'
	  val (Us, Vs) = Whnf. whnfEta UsVs
	  val (U1s, V1s) = Whnf.whnfEta U1sV1s
	in
	   (eq (G, (Us', Vs'), UsVs, sc) andalso                (* identity *)
	   (eq (G, (U1s', V1s'), U1sV1s, sc)))  	     
	  orelse
	  (eq (G, (U1s', V1s'), UsVs, sc) andalso              (* reflexivity *)
	   (eq (G, (Us', Vs'), U1sV1s, sc)))
	  orelse
	  (eq (G, (U1s', V1s'), U1sV1s, sc) andalso            (* transitivity *)
	   deriveEq (G, Q, RG', RG', Rpi, UsVs, (Us', Vs'), sc))
	  orelse
	  (eq (G, (Us', Vs'), U1sV1s, sc) andalso              (* transitivity *)
	   deriveEq (G, Q, RG, RG', Rpi, UsVs, (U1s', V1s'), sc))
	  orelse
	  deriveEq (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc)
	(* bp Mon Jan 24 13:39:28 2000 - otherwise we might end up in an infinite loop 
	   if it should fail
	 deriveEq (G, Q, 
	 RG, I.Decl(RG', Eq(R.Arg UsVs', R.Arg U1sV1s')), UsVs, U1sV1s, sc)
	 *)
	end

      | deriveEq' (G, Q, I.Decl(RG, Less(R.Arg UsVs', R.Arg U1sV1s')), 
		   RG', Rpi, UsVs, U1sV1s, sc) = 
	deriveEq' (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc) 

    (* deriveLt (G, Q, RG, RG', A, C , sc) = B

     check if A < C is derivable in RG'

     *)
    
    and deriveLt (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc) =
	  (* A < B by subterm ordering *)
	   (lt (G, Q, UsVs, U1sV1s, sc) 
	    orelse 
	    deriveLt' (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc))

    and deriveLt' (G, Q, I.Null, RG', Rpi, UsVs, U1sV1s, sc) = false
      | deriveLt' (G, Q,I.Decl(RG, Less(R.Arg UsVs', R.Arg U1sV1s')), RG', Rpi, UsVs, U1sV1s, sc) = 
          let 
	    val _ = if (!Global.chatter) >= 5 then 
	               fmtDerive (G, Less(R.Arg UsVs', R.Arg U1sV1s'), Less(R.Arg UsVs, R.Arg U1sV1s))
		    else 
		      ()
	    val (U1s', V1s') = Whnf.whnfEta U1sV1s'
	    val (Us, Vs) =  Whnf.whnfEta UsVs
	    val (Us', Vs') =  Whnf.whnfEta UsVs'
	  in 
            (*     
	       ---------------------------
	       G | Q | RG, A < B |- A < B  *)
	    (eq (G, (Us, Vs),(Us', Vs'), sc)  andalso
	     eq (G, (U1s', V1s'), U1sV1s, sc))
	  orelse
	    (* B' <= B  (G | Q | RG |- C < A  or  G | Q | RG |- C = A)
	      --------------------------------------------------------------  
 	                G | Q | RG, A < B' |- C < B    
             *)
	    ( lt (G, Q, (U1s', V1s') , U1sV1s, sc) 
	     andalso
	     (deriveLt (G, Q, RG', RG', Rpi, UsVs,(Us', Vs') , sc)   orelse 
	      deriveEq (G, Q, RG', RG', Rpi, UsVs, (Us', Vs'), sc)))
	  orelse
	    (eq (G,(U1s', V1s') , U1sV1s, sc) 
	     andalso
	     (deriveLt (G, Q, RG', RG', Rpi, UsVs,(Us', Vs') , sc)  orelse 
	      deriveEq (G, Q, RG', RG', Rpi, UsVs, (Us', Vs'), sc)))
	  orelse
	  deriveLt (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc) 

	  end
      | deriveLt' (G, Q, I.Decl(RG, Eq(R.Arg UsVs', R.Arg U1sV1s')), RG', Rpi, UsVs, U1sV1s, sc) =
	  let 
	    val _ = if (!Global.chatter) >= 5 then 
	                fmtDerive (G, Eq(R.Arg UsVs', R.Arg U1sV1s'),
				   Less(R.Arg UsVs, R.Arg U1sV1s))
		    else 
		      ()
	    val (Us',Vs') = Whnf.whnfEta UsVs'
	    val (U1s', V1s') = Whnf.whnfEta U1sV1s' 
	  in 
	    (eq (G, (Us',Vs'), UsVs, sc) andalso 
	     lt (G, Q, (U1s', V1s'), U1sV1s, sc))
	    orelse 
	    (eq (G, (U1s', V1s'), UsVs, sc) andalso 
	     lt (G, Q, (Us',Vs'), U1sV1s, sc))
	    orelse
	    (*  G | Q | RG |- C < A  andalso B <= D
	     * -------------------------------------
	     *   G | Q | RG, B = A |- C < D
             *)
	    (lt (G, Q, (U1s', V1s'), U1sV1s, sc) andalso
	       deriveLt (G, Q, RG', RG', Rpi, UsVs, UsVs', sc)) 
	  orelse
	    (*   G | Q | RG |- C < A  andalso  B <= D 
	     *  ------------------------------------- 
	     *   G | Q | RG, A = B |- C < D
             *)
	    (lt (G, Q, (Us',Vs'), U1sV1s, sc) andalso 
	       deriveLt (G, Q, RG', RG', Rpi, UsVs, U1sV1s', sc))
	   orelse
	     (* t<=1 *)
	     (eq (G, (Us',Vs'), U1sV1s, sc) andalso
	      deriveLt (G, Q, RG', RG', Rpi, UsVs, U1sV1s', sc))
	  orelse
	     (* t<=2 *)
	      (eq (G, (U1s', V1s'), U1sV1s, sc) andalso
	       deriveLt (G, Q, RG', RG', Rpi, UsVs, UsVs', sc)) 

	  orelse
	  deriveLt (G, Q, RG, RG', Rpi, UsVs, U1sV1s, sc)  
	end
		 


    (* ltinit (G, Q, RG, Rpi, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B'

       Invariant:
       B' holds  iff
            G : Q 
       and RG, Rpi is a context of reduction assumptions
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2] 
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  U[s1] is a strict subterm of U'[s1'] or  U[s1] < U'[s1']  is derivable from RG, Rpi
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
    *)
    and ltinit (G, Q, RG, Rpi, (Us, Vs), UsVs', sc) = 
          ltinitW (G, Q, RG, Rpi, Whnf.whnfEta (Us, Vs), UsVs', sc)
    and ltinitW (G, Q, RG, Rpi, (Us, Vs as (I.Root _, _)), UsVs', sc) =
          lt (G, Q, (Us, Vs), UsVs', sc) 
      | ltinitW (G, Q, RG, Rpi, ((I.Lam (_, U), s1), (I.Pi ((D, _), V), s2)), 
		 ((U', s1'), (V', s2')), sc) =
	  focusPi (I.Decl (G, N.decLUName (G, I.decSub (D, s2))),
		  I.Decl (Q, Universal), RG, Rpi,  
		  Less (R.Arg ((U, I.dot1 s1), (V, I.dot1 s2)),  
		        R.Arg ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))), sc) 

    and ltinit' (G, Q, RG, Rpi, (Us, Vs), UsVs', sc) = 
	(ltinit (G, Q, RG, Rpi, (Us, Vs), UsVs', sc)
	  orelse 
	  (let 
	     val _ = if (!Global.chatter) >= 5 then 
		       print ("\n derive " ^ 
			      F.makestring_fmt (
				fmtPredicate(G, Less(R.Arg (Us, Vs), R.Arg UsVs')))
			      ^"\n")
		     else 
		       ()
	     val B = deriveLt (G, Q, RG, RG, Rpi, (Us, Vs), UsVs', sc)
	   in
	     if (!Global.chatter) >= 5 then 
		 if B then   
		   (print ("\n derivation successful"); B)
		 else 
		   (print("\n derivation failed"); B)
	     else
	       B
	   end ))
	

    (* ordlt (G, Q, RG, Rpi, O1, O2) = B'
     
       Invariant:
       If   G : Q and RG + Rpi is a context of reduction assumptions
       and  G |- O1 augmented subterms
       and  G |- O2 not contianing any EVars
       then B' holds iff O1 is smaller than O2 
	   -bp or is derivable from RG   
    *)
    and ordlt (G, Q, RG, Rpi, R.Arg UsVs, R.Arg UsVs', sc) =  
	ltinit' (G, Q, RG, Rpi, UsVs, UsVs', sc)
      | ordlt (G, Q, RG, Rpi, R.Lex L, R.Lex L', sc) = ordltLex (G, Q, RG, Rpi, L, L', sc)
      | ordlt (G, Q, RG, Rpi, R.Simul L, R.Simul L', sc) = ordltSimul (G, Q, RG, Rpi, L, L', sc)

    (* ordltLex (G, Q, RG, Rpi, L1, L2) = B'
     
       Invariant:
       If   G : Q and RG + Rpi is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff L1 is lexically smaller than L2 
    *)
    and ordltLex (G, Q, RG, Rpi, nil, nil, sc) = false
      | ordltLex (G, Q, RG, Rpi, O :: L, O' :: L', sc) =
          ordlt (G, Q, RG, Rpi, O, O', sc) 
	  orelse 
	  (ordeq (G, Q, RG, Rpi, O, O', sc) andalso ordltLex (G, Q, RG, Rpi, L, L', sc))
      
    (* ordltSimul (G, Q, RG, Rpi, L1, L2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously smaller than L2 
    *)
    and ordltSimul (G, Q, RG, Rpi, nil, nil, sc) = false
      | ordltSimul (G, Q, RG, Rpi, O :: L, O' :: L', sc) = 
          (ordlt (G, Q, RG, Rpi, O, O', sc) andalso ordleSimul (G, Q, RG, Rpi, L, L', sc))
	  orelse 
	  (ordeq (G, Q, RG, Rpi, O, O', sc) andalso ordltSimul (G, Q, RG, Rpi, L, L', sc))

    (* ordleSimul (G, Q, RG, Rpi, L1, L2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is simultaneously less than or equal to L2 
    *)
    and ordleSimul (G, Q, RG, Rpi, nil, nil, sc) = sc ()
      | ordleSimul (G, Q, RG, Rpi, O :: L, O' :: L', sc) =
          ordle (G, Q, RG, Rpi, O, O', sc) andalso ordleSimul (G, Q, RG, Rpi, L, L', sc) 

    (* ordeq (G, Q, RG, O1, O2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff O1 is convertible to O2 
    *)
    and ordeq (G, Q, RG, Rpi, R.Arg UsVs, R.Arg UsVs', sc) =  
       conv (UsVs, UsVs')
	orelse
	(let 
	   val _ = if (!Global.chatter) >= 5 then 
	              (print ("\n ordereq derive ");
		      print(F.makestring_fmt 
			     (fmtPredicate(G, Eq(R.Arg UsVs, R.Arg UsVs')))
			     ^  "\n"))
		   else 
		        ()
	   val B = deriveEq (G, Q, RG, RG, Rpi, UsVs, UsVs', sc)
	 in
	   if (!Global.chatter) >= 5 then 
	      if B then   
		 (print ("\n derivation successful"); B)
	      else 
		 (print("\n derivation failed"); B)
	   else
	       B
	 end)
      | ordeq (G, Q, RG, Rpi, R.Lex L, R.Lex L', sc) = ordeqs (G, Q, RG, Rpi, L, L', sc)
      | ordeq (G, Q, RG, Rpi, R.Simul L, R.Simul L', sc) = ordeqs (G, Q, RG,  Rpi, L, L', sc)
      
    (* ordeqs (G, Q, RG, L1, L2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff L1 is convertible to L2 
    *)
    and ordeqs (G, Q, RG, Rpi, nil, nil, sc) = sc()
      | ordeqs (G, Q, RG, Rpi, O :: L, O' :: L', sc) = 
          ordeq (G, Q, RG, Rpi, O, O', sc) andalso ordeqs (G, Q, RG, Rpi, L, L', sc)

    (* ordeq (G, Q, RG, O1, O2) = B'
     
       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not contianing any EVars
       then B' holds iff O1 is convertible to O2 or O1 is smaller than O2 
    *)

    and ordle (G, Q, RG, Rpi, O, O', sc) = 
	ordeq (G, Q, RG, Rpi, O, O', sc) orelse ordlt (G, Q, RG, Rpi, O, O', sc)

    (* ordRight (G, Q, RG, Rpi', P, sc) = 
     *)
    and ordRight (G, Q, RG, Rpi, Less(O, O'), sc) = ordlt (G, Q, RG, Rpi, O, O', sc)
      | ordRight (G, Q, RG, Rpi, Leq(O, O'), sc) = ordle (G, Q, RG, Rpi, O, O', sc)
      | ordRight (G, Q, RG, Rpi, Eq(O, O'), sc) = ordeq (G, Q, RG, Rpi, O, O', sc)

    (* ordLeft  (G, Q, RG, P) = 

       first simplify the context RG and then the right side P
       order of RG' is reversed

       Precondition: RG does not contain any Pi-quanitfied reduction props.

       Invariant:
       If   G : Q and RG is a context of reduction assumptions
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not contianing any EVars
       then B' holds iff O1 is equal to O2 or O1 is smaller than O2 

     *)

    and ordLeft (G, Q, RG, P, sc) = 
	let 
	  fun ordLeft' (G, Q, I.Null, D, Dpi, P) = 
	      	((if (!Global.chatter) >= 5 then 
		   print ("\n transition to right " ^ (F.makestring_fmt (fmtPredicate(G,P)))
			  ^ "\n") 
		 else 
		    ());
		 ordRight (G, Q, D, Dpi, P, sc))
	    | ordLeft' (G, Q, I.Decl(D, Less(R.Arg UsVs', R.Arg U1sV1s')), D', Dpi, P) = 
	        ordLeft' (G, Q, D, I.Decl(D', Less(R.Arg UsVs', R.Arg U1sV1s')), Dpi, P)
	    | ordLeft' (G, Q, I.Decl(D, Eq(R.Arg UsVs', R.Arg U1sV1s')), D', Dpi, P) = 
		ordLeft' (G, Q, D, I.Decl(D', Eq(R.Arg UsVs', R.Arg U1sV1s')), Dpi, P)
          (* Leq *)
	    | ordLeft' (G, Q, I.Decl(D, Leq(O, O')), D', Dpi, P) = 
		ordLeft' (G, Q, I.Decl(D, Less (O, O')), D', Dpi, P)
 	        andalso 
		ordLeft' (G, Q, I.Decl(D, Eq (O, O')), D', Dpi, P)
	  (* Lexicograqhic *)
	  (* Equality *)
	    | ordLeft' (G, Q, I.Decl (D, Eq(R.Lex [], R.Lex [])), D', Dpi, P) = 
		ordLeft' (G, Q, D, D', Dpi, P)
	    | ordLeft' (G, Q, I.Decl (D, Eq(R.Lex (O::Olist), R.Lex (O'::O'list))), D', Dpi, P) = 
		ordLeft' (G, Q, I.Decl(I.Decl (D, Eq(O, O')), Eq(R.Lex Olist, R.Lex O'list)), D', Dpi, P)
	  (* Less *)
	    | ordLeft' (G, Q, I.Decl (D, Less(R.Lex [], R.Lex [])), D', Dpi, P) = 
		ordLeft' (G, Q, D, D', Dpi, P)
	    | ordLeft' (G, Q, I.Decl (D, Less(R.Lex (O::Olist), R.Lex (O'::O'list))), D', Dpi, P) = 
		ordLeft' (G, Q, I.Decl (D, Less(O, O')), D', Dpi, P)
		andalso 
 		ordLeft' (G, Q, I.Decl(I.Decl (D, Eq(O, O')), Less (R.Lex Olist, R.Lex O'list)), D', Dpi, P)
	  (* Simultanous *)
	  (* Equality *)
	    | ordLeft' (G, Q, I.Decl (D, Eq(R.Simul [], R.Simul [])), D', Dpi, P) = 
		ordLeft' (G, Q, D, D', Dpi, P)
	    | ordLeft' (G, Q, I.Decl (D, Eq(R.Simul (O::Olist), R.Simul (O'::O'list))), D', Dpi, P) = 
		ordLeft' (G, Q, I.Decl(I.Decl (D, Eq(O, O')), Eq(R.Simul Olist, R.Simul O'list)), D', Dpi, P)
	  (* Less *)
	    | ordLeft' (G, Q, I.Decl (D, Less(R.Simul [], R.Simul [])), D', Dpi, P) = 
		ordLeft' (G, Q, D, D', Dpi, P)
	    | ordLeft' (G, Q, I.Decl (D, Less(R.Simul (O::Olist), R.Simul (O'::O'list))), D', Dpi, P) = 
		ordLeft' (G, Q, I.Decl(I.Decl (D, Less(O, O')),Leq (R.Simul Olist, R.Simul O'list)), D', Dpi, P)
		andalso 
		ordLeft' (G, Q, I.Decl(I.Decl (D, Eq(O, O')), Less (R.Simul Olist, R.Simul O'list)), D', Dpi, P)
	    (* Pi *)
	    | ordLeft' (G, Q, I.Decl (D, P' as Pi(_, _)), D', Dpi, P) = 
		ordLeft' (G, Q, D, D', I.Decl(Dpi, P'), P)
	in
	   ordLeft' (G, Q, RG, I.Null, I.Null, P)
	end
    
    and focusPi (G, Q, RG, I.Null, P, sc) = 
	(* multiplicity = 1 *)
        ((if (!Global.chatter) >= 5 then 
	   print ("\n Pi instantiated with existential vars - ")
	 else 
	    ());
	 ordLeft (G, Q, RG, P, sc))
      | focusPi (G, Q, RG, I.Decl(Rpi, Pi(D as I.Dec(_, V), P)), P', sc) =
	  let
	    val X = I.newEVar (G, V) 
	    val sc' = fn () => (isParameter (Q, X); sc ())	      
	    fun plus1 (I.Shift n) = I.Shift (n + 1)
	      | plus1 (I.Dot(I.Exp X, s)) = I.Dot(I.Exp X, plus1 s)
	      | plus1 (I.Dot (I.Idx n, s)) = I.Dot (I.Idx n, s)

	    val P1 = shiftP P (fn s => case s of I.Shift n => I.Dot(I.Exp X, I.Shift n)
                        	  | I.Dot(I.Exp _, s') => I.Dot (I.Exp(X), plus1 s)
				  | I.Dot(I.Idx n, s') => I.Dot(I.Exp X, I.Dot(I.bvarSub (n, s'), s')))     
	  in
	    focusPi (G, Q, RG, I.Decl(Rpi, P1), P', sc')
	  end 	     
      | focusPi (G, Q, RG, I.Decl(Rpi, Less(O, O')), P', sc) =
	  ((if (!Global.chatter) >= 5 then 
	      (print ("\n pi reduction predicate is" );
	       print (F.makestring_fmt (fmtPredicate(G,Less(O ,O'))));  
	       print ("\n to show: " ^ (F.makestring_fmt (fmtPredicate(G, P')))))
	    else ());
	   focusPi (G, Q, I.Decl(RG, Less(O ,O')), Rpi, P', sc))
      | focusPi (G, Q, RG, I.Decl(Rpi, Leq(O, O')), P', sc) =
	  ((if (!Global.chatter) >= 5 then 
	      (print ("\n pi reduction predicate is " ^ 
		      (F.makestring_fmt (fmtPredicate(G,Leq(O ,O' ))))^ "\n");
	       print ("\n to show: " ^ (F.makestring_fmt (fmtPredicate(G,P')))))
	      else ());
	      focusPi (G, Q, I.Decl(RG,Leq(O, O')), Rpi, P', sc))
      | focusPi (G, Q, RG, I.Decl(Rpi, Eq(O1, O2)), P',sc) =
	   ((if (!Global.chatter) >= 5 then 
	       (print ("\n pi reduction predicate is " );
		print (F.makestring_fmt (fmtPredicate(G,Eq(O1 ,O2))));  
		print ("\n to show: " ^ (F.makestring_fmt (fmtPredicate(G, P')))))
	     else ());  
	       focusPi (G, Q, I.Decl(RG, Eq(O1, O2)), Rpi, P', sc))


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
	  val P = select (a, (S, s))
	  val P' = select (a', (S', s'))
	  val a's = R.mutLookup a
	  val _ = R.selLookup a'   (* check if a' terminates *)	 
	  (* -bp reduction predicate *)
	  val RG' = ((if (!Global.chatter) >= 5 then  
			 print ("\n reduction predicate " ^ 
				F.makestring_fmt (
				  fmtPredicate(G, selectROrder (a, (S, s)) ))^
				" added to context\n") 
			 else ()) 
		     ;   I.Decl(RG, selectROrder (a, (S, s))) ) 
               handle R.Error(msg) =>    
			(if (!Global.chatter) >= 5 then  
			   (print ("\n no reduction predicate defined for "^
                                     I.conDecName (I.sgnLookup a));
                            RG ) 
			 else 
	                    RG)                     			     
	in
	  case lookup (a's, fn x' => x' = a') 
	    of R.Empty => RG' 
	     | R.LE _ =>  
	      (if ordLeft (G, Q, RG, Leq(P, P'), init) then 
		 (if (!Global.chatter) >= 5 then  
		   (print  ("\n ordLeft on " ^ 
                            F.makestring_fmt (
                              fmtComparison (G, P, "<=", P')) ^ "\n");  
		    RG') 
		 else RG') 
	       else raise Error' (occ, "Termination violation:\n" 
				       ^ F.makestring_fmt (fmtComparison (G, P, "<=", P'))) 
		   ) 
	     | R.LT _ =>  
	      (if ordLeft (G, Q, RG, Less(P, P'), init) then   
		 (if (!Global.chatter) >= 5 then  
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
	(((if (!Global.chatter) >= 5 then 
	    (print ("\n reduction predicate " ^ I.conDecName (I.sgnLookup a) ^ " red. order added");
	    print ("\n reduction predicate is " ^ (F.makestring_fmt (fmtPredicate(G, selectROrder (a, (S, s))))) ^ "\n"))
	  else ());
	    I.Decl(RG', selectROrder (a, (S, s))))
	     handle R.Error(s) => 
	       (if (!Global.chatter) >= 5 then 
		  (print ("\n no reduction predicate defined for " ^ I.conDecName (I.sgnLookup a));RG )
		else
		  RG'))
	    
       | checkRImpW (G, Q, RG, RG', (I.Pi ((D, I.Maybe), V), s), occ) = 
	    let 
	      val RG'' = checkRImp (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
				    I.Decl (Q, Universal), RG, RG', (V, I.dot1 s), P.body occ)
	      val _ = if (!Global.chatter) >= 5 then 
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
	       val _ = if (!Global.chatter) >= 5 then 
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
	  val RO = selectROrder(a, (S, s))
	  val _ = ((if (!Global.chatter) >= 5 then 
			 (print ("\n check reduction predicate ");
			  print (fmtRGCtx(G, RG) ^ " |- " ^  
				 (F.makestring_fmt (fmtPredicate(G, RO))) ^ " \n"))
			 else ())
	             handle R.Error(s) => 
			(if (!Global.chatter) >= 5 then 
			  print ("\n no reduction predicate defined for " ^ I.conDecName (I.sgnLookup a))
			 else
	                    ()))    
	(* add mutual look up! - bp *)
	(* not needed; done automatically ...  -bp1/31/00.*)
	(* val RG' = I.Decl(RG, selectROrder (a, (S, s))) *)
	in
	  case RO
	    of Less(O, O') => 
	       if ordLeft(G, Q, RG, Less(O, O'), init) then 
		 if (!Global.chatter) >= 5 then 
		     (print  ("\n" ^ F.makestring_fmt 
			      (fmtComparison (G, O, "<", O')) ^ "\n"))
		 else
		     ()
	       else  raise Error' (occ, "Reduction violation:\n" ^ F.makestring_fmt 
				   (fmtComparison (G, O, "<", O')))
	  | Leq(O, O') =>  
	     if ordLeft(G, Q, RG, Leq(O, O'), init) then 
	      if (!Global.chatter) >= 5 then 
		  (print  ("\n" ^ F.makestring_fmt 
			   (fmtComparison (G, O, "<=", O')) ^ "\n"))
	      else
		  ()
	     else  raise Error' (occ, "Reduction violation:\n" ^ F.makestring_fmt 
				 (fmtComparison (G, O, "<=", O')))

           | Eq(O, O') =>  
	      if ordLeft (G, Q, RG, Eq(O, O'), init) then 
	        if (!Global.chatter) >= 5 then 
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
	  fun checkFam' nil = ()
	    | checkFam' (I.Const b::bs) = 
		(if (!Global.chatter) >= 4 then 
		   print ("[" ^ N.constName b ^ ":")
		 else ();
		 (* reuse variable names when tracing *)
		 if (!Global.chatter) >= 5 then N.varReset () else ();
		 ((if (!Global.chatter) >= 5 
		     then print ("\nTermination Check successful") 
		    else ());
		   (checkClause (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top);
		    checkReduction (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top))
		    handle Error' (occ, msg) => error (b, occ, msg)
			 | R.Error (msg) => raise Error (msg));
		 if (!Global.chatter) >= 4
		   then print ("]\n")
		 else ();
		 checkFam' bs)
	  val _ = if (!Global.chatter) >= 4
		    then print "[Reduces: "
		  else ()
	in
	  (checkFam' (Index.lookup a);
	   if (!Global.chatter) >= 4 then 
	     print "]\n" else ())
	end

    fun checkFam a =
	let 
	  fun checkFam' nil = ()
	    | checkFam' (I.Const b::bs) = 
		(if (!Global.chatter) >= 4 then 
		   print ("[" ^ N.constName b ^ ":")
		 else ();
		 (* reuse variable names when tracing *)
		 if (!Global.chatter) >= 5 then N.varReset () else ();
	        (checkClause (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top)
		 handle Error' (occ, msg) => error (b, occ, msg)
		      | Order.Error (msg) => raise Error (msg));
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

    fun reset () = (R.reset(); R.resetROrder())

  in
    val reset = reset
    (* val check = fn Vs => checkClause (I.Null, I.Null, Vs, P.top) *)
    val checkFamReduction = checkFamReduction 
    val checkFam = checkFam  
  end (* local *)
end; (* functor Reduces  *)
