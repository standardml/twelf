(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
(* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see 
   tech report CMU-CS-01-115
 *)

functor Reduces    (structure Global : GLOBAL
		   structure IntSyn': INTSYN
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = IntSyn'
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
		   structure Checking : CHECKING
		      sharing Checking.Order = Order
		      sharing Checking.IntSyn = IntSyn'
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
    structure C = Checking

    exception Error' of P.occ * string

    fun error (c, occ, msg) =  
        (case Origins.originLookup c
	   of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) => 
		raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                                         Origins.linesInfoLookup (fileName),
                                         msg)))


   (*--------------------------------------------------------------------*)
   (* Printing *)

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
        F.HOVbox0 1 0 1 [fmtOrder (G, O), F.Break, F.String comp, 
			 F.Break, fmtOrder (G, O')]


    fun fmtPredicate (G, C.Less(O, O')) = fmtComparison (G, O, "<", O')
      | fmtPredicate (G, C.Leq(O, O'))  = fmtComparison (G, O, "<=", O')
      | fmtPredicate (G, C.Eq(O, O'))  = fmtComparison (G, O, "=", O')
      | fmtPredicate (G, C.Pi(D, P))  =  
          F.Hbox [F.String "Pi ", 
		  fmtPredicate (I.Decl(G, D), C.shiftPred P (fn s => I.dot1 s))]

    fun ctxToString (G, I.Null) = ""
      | ctxToString (G, I.Decl(I.Null, P)) = 
	F.makestring_fmt(fmtPredicate (G, P) )
      | ctxToString (G, I.Decl(RG, P)) = 
	F.makestring_fmt(fmtPredicate (G, P)) ^ " ," ^ ctxToString(G, RG)

    fun orderToString (G, P) = F.makestring_fmt(fmtPredicate (G, P))

   (*--------------------------------------------------------------------*)
   fun append (I.Null, G) = G
     | append (G, I.Null) = G
     | append (G, I.Decl(G', P)) = 
         append (I.Decl(G, P), G')

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
	  raise Error' (occ, "Termination violation: no order assigned for " ^ 
			N.qidToString (N.constQid c))

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
	  fun select' (R.Arg n) = R.Arg (select'' (n, ((S, s), Vid)))
	    | select' (R.Lex L) = R.Lex (map select' L)
	    | select' (R.Simul L) = R.Simul (map select' L)

	  fun selectP (R.Less(O1, O2)) = C.Less(select' O1, select' O2)
	    | selectP (R.Leq(O1, O2)) = C.Leq(select' O1, select' O2)
	    | selectP (R.Eq(O1, O2)) = C.Eq(select' O1, select' O2)
	in
	  SOME(selectP (R.selLookupROrder c)) handle R.Error(s) => NONE
	end

   (*--------------------------------------------------------------*)

    (* abstractRedCtx (G, RG, n, D) = RG''
       Invariant: 
         
       If  G, x : V1 |- RG   
         and for all P in RG. G, x : V1 |- P
       then G |- RG' 
	 and for all P in RG'. G |- Pi x:V1 . P
        
    *)
      
    fun abstractRedCtx (G, RG, D as I.Dec(_, V1)) = 
        let 
	  fun bind (I.Null, RG) = RG
	    | bind (I.Decl(RG, P), RG') = 
	      (print "\n WARNING: Quantified order: ";
	       print (orderToString (G, C.Pi(D, P)));
	       print "\n The reduction checker may be incomplete! \n ";
	       bind(RG, I.Decl(RG', C.Pi(D, P))))
	in
	  bind (RG, I.Null)
	end 

  
    (*--------------------------------------------------------------------*)
    (* Termination Checker *)

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
    fun checkGoal (G, Q, RG, Vs, Vs', occ) = 
         checkGoalW (G, Q, RG, Whnf.whnf Vs, Vs', occ)

    and checkGoalW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), (V', s'), occ) =
        let
	  val _ = checkClause (G, Q, RG, (V1, s), P.label occ)
	in
	    checkGoal (I.Decl (G, I.decSub (D, s)),
		       I.Decl (Q, C.Universal), RG,   
		       (V2, I.dot1 s), 
		       (V', I.comp (s', I.shift)), P.body occ)
	end

      | checkGoalW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), (V', s'), occ) =
          checkGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
		     I.Decl (Q, C.Universal), RG, 
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
	  val P = select (a, (S, s))	(* only if a terminates? *)
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ 
			     N.qidToString (N.constQid a))
	  val P' = select (a', (S', s')) (* always succeeds? -fp *)
	  (*
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ 
			     N.qidToString (N.constQid a'))
          *)
	  val a's = Order.mutLookup a	(* always succeeds? -fp *)
	  (*
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ 
			     N.qidToString (N.constQid a))
	  *)
	  (* 
	  val _ = Order.selLookup a'
	  *)
	  (* check if a' terminates --- should always succeed? -fp *)
	  (*
	    handle Order.Error (msg)
	    => raise Error' (occ, "Termination violation: no order assigned for " ^ 
			     N.qidToString (N.constQid a))
          *)
	  val RG' = (case selectROrder (a, (S, s)) 
	               of NONE => (if (!Global.chatter) > 5 
				     then  print ("\n no reduction predicate defined for "^
						  N.qidToString (N.constQid a) ^ "\n")
				   else ();
				     RG)
		       | SOME(O) => (if (!Global.chatter) > 5 
				       then print ("\n reduction predicate " ^ 
						   orderToString (G, O) ^
						   " added to context\n") 
				     else ();
				     I.Decl(RG, O))) 
	in
	  case lookup (a's, fn x' => x' = a') 
	    of R.Empty => RG' 
	     | R.LE _ => (if (!Global.chatter) >= 5 
			    then print ("\n check termination order: " ^ ctxToString (G, RG) ^ 
					" ---> " ^ orderToString (G, C.Leq(P, P')) ^ "\n")
			  else ();
			    if C.deduce (G, Q, RG, C.Leq(P, P')) 
			      then RG'
			    else raise Error' (occ, "Termination violation:\n" ^ 
					       ctxToString (G, RG) ^ 
					       " ---> " ^ 
					       orderToString (G, C.Leq(P, P'))))
	     | R.LT _ =>  (if (!Global.chatter) >= 5 
			    then  print  ("\n check termination order " ^ 
					   ctxToString (G, RG) ^ " ---> " ^ 
					   orderToString (G, C.Less(P,P')) ^ 
					   "\n")
			   else ();
			   if C.deduce (G, Q, RG, C.Less(P, P')) 
			     then RG'
			   else raise Error' (occ, "Termination violation:\n" ^ 
					       ctxToString (G, RG) ^ " ---> " ^
					       orderToString (G, C.Less(P, P'))))
	end 

    (* checkImp (G, Q, RG, (V1, s1), (V2, s2), occ) = RG'
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and RG is a context for derived reduction order assumptions 
       and  G |- RG

       then RG' if V1[s1]  is "smaller" then  V2[s2]
    *)
    and checkImp (G, Q, RG, Vs, Vs', occ) = 
         checkImpW (G, Q, RG, Vs, Whnf.whnf Vs', occ)

    and checkImpW (G, Q, RG, (V, s), (I.Pi ((D', I.No), V'), s'), occ) =
          checkImp (I.Decl (G, I.decSub (D', s')),
		    I.Decl (Q, C.Existential), RG, 
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, RG, (V, s), (I.Pi ((D', I.Maybe), V'), s'), occ) =
          checkImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		    I.Decl (Q, C.Existential), RG, 
		    (V, I.comp (s, I.shift)), (V', I.dot1 s'), occ)
      | checkImpW (G, Q, RG, Vs, Vs' as (I.Root (I.Const a, S), s), occ) = 
	  checkGoal (G, Q, RG, Vs, Vs', occ)
      | checkImpW (G, Q, RG, Vs, (I.Root (I.Def a, S), s), occ) =
	  raise Error' (occ, "Termination checking for defined type families not yet available:\n"
			^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


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
    and checkClause (G, Q, RG, Vs, occ) = 
         checkClauseW (G, Q, RG, Whnf.whnf Vs, occ)

    and checkClauseW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), occ) =
	  checkClause (I.Decl(G, N.decEName (G, I.decSub (D, s))), 
		       I.Decl (Q, C.Existential), RG, 
		       (V, I.dot1 s), P.body occ)
      | checkClauseW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
        let 
	  val RG' = checkClause (I.Decl (G, I.decSub (D, s)),
				 I.Decl (Q, C.Existential), RG, 
				 (V2, I.dot1 s), P.body occ)
	in 
          checkImp (I.Decl (G, I.decSub (D, s)),
		    I.Decl (Q, C.Existential), RG', (V1, I.comp (s, I.shift)), 
		    (V2, I.dot1 s), P.label occ)
	end
      | checkClauseW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), occ) = RG
      | checkClauseW (G, Q, RG, (I.Root (I.Def a, S), s), occ) =
	raise Error' (occ, "Termination checking for defined type families not yet available:\n"
		      ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")



    (*-------------------------------------------------------------------*)
    (* Reduction Checker *) 

    (* getROrder (G, Q, (V, s)) = O
       If G: Q  
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)
    fun getROrder (G, Q, Vs) = getROrderW (G, Q, Whnf.whnf Vs)
    and getROrderW (G, Q, Vs as (I.Root (I.Const a, S), s)) = 
         let
	   val O = selectROrder (a, (S, s))
	   val _ = case O 
	            of NONE => if (!Global.chatter) > 5 
				 then print ("\n no reduction predicate defined for " ^ 
					     N.qidToString (N.constQid a))
			       else
				 ()
	             | SOME(O) => if (!Global.chatter) > 5 
				       then print ("\n reduction predicate for " ^ 
						   N.qidToString (N.constQid a) ^ 
						   " added : " ^ 
						   orderToString (G, O))
				      else ()
	 in 
	   O
	 end 
      | getROrderW (G, Q, (I.Pi ((D, I.Maybe), V), s)) = 
	  let 
	    val O = getROrder (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
			       I.Decl (Q, C.Universal), (V, I.dot1 s))
 	  in 
	    case O 
	      of NONE => NONE
	       | SOME(O') => SOME(C.Pi(D, O'))
	  end 
      | getROrderW (G, Q, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s)) = 
	  let
	    val O = getROrder (I.Decl (G, I.decSub (D, s)),
			       I.Decl (Q, C.Existential), (V2, I.dot1 s))
	  in 
	    case O 
	      of NONE => NONE 
	       | SOME(O') => SOME(C.shiftPred O' (fn s => I.comp(s, I.invShift)))
	  end 
      | getROrderW (G, Q, Vs as (I.Root (I.Def a, S), s)) = 
	  raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
			^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")



    (* checkRGoal (G, Q, RG, (V1, s1), occ) = RG''
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and RG is a context of reduction predicates 
       and  G |- RG 
       and RG implies that V1[s1] satisfies its associated reduction order

     *)

     fun checkRGoal (G, Q, RG, Vs, occ) = 
           checkRGoalW (G, Q, RG, Whnf.whnf Vs, occ)

     and checkRGoalW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), occ) = () (* trivial *)
            
       | checkRGoalW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), occ) = 
           checkRGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))), 
		      I.Decl (Q, C.Universal), 
		      C.shiftRCtx RG (fn s => I.comp(s, I.dot1 s)),
		      (V, I.dot1 s), P.body occ)

       | checkRGoalW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) = 
	   (checkRClause (I.Decl (G, N.decLUName (G, I.decSub (D, s))),  
			  I.Decl (Q, C.Universal), 
			  C.shiftRCtx RG (fn s => I.comp(s, I.shift)),
			  (V1, I.comp(s, I.shift)), P.label occ);
	    checkRGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))),
			I.Decl (Q, C.Universal), 
			C.shiftRCtx RG (fn s => I.comp(s, I.shift)), 
			(V2, I.dot1 s), P.body occ))

       | checkRGoalW (G, Q, RG, (I.Root (I.Def a, S), s), occ) =
	   raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
			 ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


    (* checkRImp (G, Q, RG, (V1, s1), (V2, s2), occ) = ()
       
       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and RG is a context for derived reduction order assumptions 
       and G |- RG

       then RG implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)

    and checkRImp (G, Q, RG, Vs, Vs', occ) = 
         checkRImpW (G, Q, RG, Whnf.whnf Vs, Vs', occ)

    and checkRImpW (G, Q, RG, (I.Pi ((D', I.Maybe), V'), s'), (V, s), occ) =
          checkRImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
		     I.Decl (Q, C.Existential), 
		     C.shiftRCtx RG (fn s => I.comp(s, I.shift)), 
		     (V', I.dot1 s'), (V, I.comp (s, I.shift)), occ)
      | checkRImpW (G, Q, RG, (I.Pi ((D' as I.Dec (_, V1), I.No), V2), s'), (V, s), occ) =
	  let
	    val G' = I.Decl (G, I.decSub (D', s'))
	    val Q' = I.Decl (Q, C.Existential)
	    val RG' = C.shiftRCtx RG (fn s => I.comp(s, I.shift))
	    val RG'' = case getROrder (G', Q', (V1, I.comp(s', I.shift)))
	                 of NONE => RG'
		       | SOME(O) => I.Decl(RG', O)
	  in 
	    checkRImp (G', Q', RG'', 
		    (V2, I.dot1 s'), (V, I.comp (s, I.shift)), occ)
	  end 
      | checkRImpW (G, Q, RG, Vs' as (I.Root (I.Const a, S), s),  Vs, occ) = 
	  checkRGoal (G, Q, RG, Vs, occ)
      | checkRImpW (G, Q, RG, Vs' as (I.Root (I.Def a, S), s), Vs, occ) =
	  raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
			^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


    (* checkRClause (G, Q, RG, (V, s)) = ()

       Invariant:
       If G: Q  
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  RG is a context of reduction predicates
       and  G |- RG
       then RG implies that V[s] satifies the reduction order
    *)

    and checkRClause (G, Q, RG, Vs, occ) = checkRClauseW (G, Q, RG, Whnf.whnf Vs, occ)

    and checkRClauseW (G, Q, RG, (I.Pi ((D, I.Maybe), V), s), occ) = 
	  checkRClause (I.Decl (G, N.decEName (G, I.decSub (D, s))), 
			I.Decl (Q, C.Existential),
			C.shiftRCtx RG (fn s => I.comp(s, I.shift)), 
			(V, I.dot1 s), P.body occ)

      | checkRClauseW (G, Q, RG, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
	 let
	   val G' = I.Decl (G, I.decSub (D, s))  (* N.decEName (G, I.decSub (D, s)) *)
	   val Q' = I.Decl (Q, C.Existential) (* will not be used *)
	   val RG' = C.shiftRCtx RG (fn s => I.comp(s, I.shift))
	   val RG'' = case getROrder (G', Q', (V1, I.comp (s, I.shift)))
	                of NONE => RG'
		         | SOME(O) => I.Decl(RG', O)
	 in 
 	  checkRClause (G', Q', RG'', (V2, I.dot1 s), P.body occ); 
	  checkRImp (G', Q', RG'', (V2, I.dot1 s), (V1, I.comp(s, I.shift)), P.label occ)
	end
      | checkRClauseW (G, Q, RG, Vs as (I.Root (I.Const a, S), s), occ) =
	let 
	  val RO = case selectROrder (a, (S, s))
	             of NONE => raise Error' (occ, "No reduction order assigned for " ^ 
					      N.qidToString (N.constQid a) ^ ".")
		      | SOME(O) => O
	  val _ = if (!Global.chatter) > 5
		    then print ("\n check reduction predicate\n " ^
				ctxToString (G, RG) ^ " ---> " ^  
				orderToString (G, RO) ^ " \n")
		  else ()
	in
	  if C.deduce(G, Q, RG, RO)
	    then ()
	  else raise Error' (occ, "Reduction violation:\n" ^ 
			     ctxToString (G, RG) ^ " ---> " ^  (* rename ctx ??? *)
			     orderToString (G, RO))
	end
      | checkRClauseW (G, Q, RG, VS as (I.Root (I.Def a, S), s), occ) =
	raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
		      ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")

    (* checkFamReduction a = ()
       
       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a does not fulfill
       specified reducation property
       
       Note: checking reduction is a separate property of termination
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
		 (( checkRClause (I.Null, I.Null, I.Null, (I.constType (b), I.id), P.top))
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

    (* checkFam a = ()
       
       Invariant:
       a is name of type family in the signature
       raises invariant, if clauses for a do not terminate  
       according to specified termination order

       Note: termination checking takes into account proven 
             reduction properties.
    *)

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
