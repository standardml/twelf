(* Splitting : Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTPSplitting (structure MTPGlobal : MTPGLOBAL
		      structure Global : GLOBAL
		      structure IntSyn : INTSYN
		      structure FunSyn : FUNSYN
			sharing FunSyn.IntSyn = IntSyn
		      structure StateSyn' : STATESYN
			sharing StateSyn'.FunSyn = FunSyn
		      structure MTPAbstract : MTPABSTRACT
			sharing MTPAbstract.IntSyn = IntSyn
		        sharing MTPAbstract.StateSyn = StateSyn'
		      structure MTPrint : MTPRINT
		        sharing MTPrint.StateSyn = StateSyn'
		      structure Names : NAMES            (* too be removed  -cs *)
			sharing Names.IntSyn = IntSyn    (* too be removed  -cs *)
		      structure Conv :CONV
			sharing Conv.IntSyn = IntSyn
		      structure Whnf : WHNF
  		        sharing Whnf.IntSyn = IntSyn
		      structure TypeCheck : TYPECHECK
			sharing TypeCheck.IntSyn = IntSyn
		      structure FunTypeCheck :FUNTYPECHECK
			sharing FunTypeCheck.FunSyn = FunSyn
		      structure Index : INDEX
		        sharing Index.IntSyn = IntSyn
		      structure Print : PRINT
		        sharing Print.IntSyn = IntSyn
		      structure Unify : UNIFY
		        sharing Unify.IntSyn = IntSyn) 
  : MTPSPLITTING =
struct
  structure StateSyn = StateSyn'

  exception Error of string

  (* Invariant: 
     Case analysis generates a list of successor states 
     (the cases) from a given state.

     'a flag marks cases where unification of the types
     succeeded as "Active", and cases where there were
     leftover constraints after unification as "Inactive".
     
     NB: cases where unification fails are not considered

     Consequence: Only those splitting operators can be
     applied which do not generate inactive cases (this
     can be checked for a given operator by applicable)
  *)
  datatype 'a flag = 
    Active of 'a | InActive

  type operator = (StateSyn.State * int) * 
		   StateSyn.State flag list

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn


    (* aux (G, B) = L' 
       
       Invariant:
       If   . |- G ctx
       and  G |- B tags
       then . |- L' = GxB lfctx
    *)

    fun aux (I.Null, I.Null) = I.Null
      | aux (I.Decl (G, D), I.Decl (B, S.Lemma _)) = 
          I.Decl (aux (G, B), F.Prim D)
      | aux (G as I.Decl (_, D), B as I.Decl (_, S.Parameter (SOME l))) = 
	let
	  val F.LabelDec  (name, _, G2) = F.labelLookup l
	  val (Psi', G') = aux' (G, B, List.length G2)
	in
	  I.Decl (Psi', F.Block (F.CtxBlock (SOME l, G')))
	end

    and aux' (G, B, 0) = (aux (G, B), I.Null)
      | aux' (I.Decl (G, D), I.Decl (B, S.Parameter (SOME _)), n) =
        let
	  val (Psi', G') = aux' (G, B, n-1)
	in
	  (Psi', I.Decl (G', D))
	end



    (* conv ((G, s), (G', s')) = B
 
       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
    fun conv (Gs, Gs') =
      let
	exception Conv
	fun conv ((I.Null, s), (I.Null, s')) = (s, s') 
	  | conv ((I.Decl (G, I.Dec (_, V)), s),
		  (I.Decl (G', I.Dec (_, V')), s')) =
            let 
	      val (s1, s1') = conv ((G, s), (G', s'))
	      val ps as (s2, s2') = (I.dot1 s1, I.dot1 s1')
	    in 
	      if Conv.conv ((V, s1), (V', s1')) then ps
	      else raise Conv
	    end
	  | conv _ = raise Conv
      in
	(conv (Gs, Gs'); true) handle Conv => false
      end



    (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic  
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Uni I.Type, s)) = (I.Nil, Vs) (* s = id *)
      | createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =  
	let 
	  val X = I.newEVar (G, I.EClo (V1, s))
	  val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
	in
	  (I.App (X, S), Vs)
	end

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant: 
       If   S |- c : Pi {V1 .. Vn}. V 
       then . |- U' = c @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H) = 
      let
	val cid = (case H 
	             of (I.Const cid) => cid
		      | (I.Skonst cid) => cid)
	val V = I.constType cid
	val (S, Vs) = createEVarSpine (G, (V, I.id))
      in
	(I.Root (H, S), Vs)
      end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant: 
       If   G |- k : Pi {V1 .. Vn}. V 
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
      let
	val I.Dec (_, V) = I.ctxDec (G, k)
	val (S, Vs) = createEVarSpine (G, (V, I.id))
      in
	(I.Root (I.BVar (k), S), Vs)
      end


    (* someEVars (G, G1, s) = s'
     
       Invariant:
       If   |- G ctx
       and  G |- s : G'
       then G |- s' : G', G1

       Remark: This is someEVars from recursion.fun with a generalized ih --cs
    *)

    fun someEVars (G, nil, s) =  s
      | someEVars (G, I.Dec (_, V) :: L, s) = 
          someEVars(G, L, I.Dot (I.Exp (I.newEVar (G, I.EClo (V, s))), s))




    (* ctxSub (G, s) = G'
	     
       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)

    fun ctxSub (nil, s) = nil
      | ctxSub (D :: G, s) = I.decSub (D, s) :: ctxSub (G, I.dot1 s)



    fun createTags (0, l) = I.Null
      | createTags (n, l) = 
           I.Decl (createTags (n-1, l),  S.Parameter (SOME l))


    (* constCases (G, (V, s), I, abstract, ops) = ops'
     
       Invariant:
       If   G |- s : G'  G' |- V : type
       and  I a list of of constant declarations
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
	 operators from I
    *)
    fun constCases (G, Vs, nil, abstract, ops) = ops
      | constCases (G, Vs, I.Const c::Sgn, abstract, ops) = 
	let
	  val (U, Vs') = createAtomConst (G, I.Const c)
	  val _ = TextIO.print ("Trying Constant " ^ (I.conDecName (I.sgnLookup c)) ^ "\n")
	in
	  constCases (G, Vs, Sgn, abstract,
		      Trail.trail (fn () => 
				   (if Unify.unifiable (G, Vs, Vs')
				      then Active (abstract U)
					   :: ops
				    else ops)
				   handle  MTPAbstract.Error _ => InActive :: ops))
	end

    (* paramCases (G, (V, s), k, abstract, ops) = ops'
     
       Invariant:
       If   G |- s : G'  G' |- V : type
       and  k a variable
       and  abstract an abstraction function
       and  ops a list of possible splitting operators
       then ops' is a list extending ops, containing all possible
	 operators introduced by parameters <= k in G
    *)
    fun paramCases (G, Vs, 0, abstract, ops) = ops
      | paramCases (G, Vs, k, abstract, ops) = 
	let 
	  val (U, Vs') = createAtomBVar (G, k)
 val _ = TextIO.print ("Trying parameter " ^ (Int.toString k) ^ "\n")
	in
	  paramCases (G, Vs, k-1, abstract, 
		      Trail.trail (fn () =>
				   (if Unify.unifiable (G, Vs, Vs')
				      then Active (abstract U) :: ops
				    else ops)
				      handle  MTPAbstract.Error _ => InActive  :: ops))
	end


    fun constAndParamCases ops0 (c, G, k, (V, s'), abstract)  = 
          constCases (G, (V, s'), Index.lookup c, abstract, 
		      paramCases (G, (V, s'), k, abstract, ops0))


    fun metaCases (d, ops0) (c, G, k, Vs, abstract) =
      let
	val g = I.ctxLength G

	fun select (0, ops)  = ops
	  | select (d', ops) = 
	    let  
	      val n = g-d'+1
	      val I.Dec (_, V) = I.ctxDec (G, n)
	      val ops' = if I.targetFam V = c then 
		        let 
			  val _ = TextIO.print "Parameter context candidate found\n"
			  val (U, Vs') = createAtomBVar (G, n)
			  val _ = TextIO.print ("Unifying " ^ (Print.expToString (G, I.EClo Vs)) ^ " with " ^
			    (Print.expToString (G, I.EClo Vs')) ^ "\n")
			in
			  Trail.trail (fn () =>
				       (if Unify.unifiable (G, Vs, Vs')
					  then (TextIO.print "Success!\n"; Active (abstract U) :: ops) (* abstract state *)
					else ops)
					  handle MTPAbstract.Error _ => InActive :: ops)
			end
		      else ops
	    in 
	      select (d'-1, ops')
	    end
      in
	select (d, ops0)
      end

          
fun inspect (I.Shift k) = TextIO.print ("^" ^ (Int.toString k))
  | inspect (I.Dot (I.Idx n, s)) = (TextIO.print ("(" ^ (Int.toString n) ^ ")"); inspect s)
  | inspect (I.Dot (I.Exp _, s)) = (TextIO.print ("X"); inspect s)
  


    (* lowerSplitDest (G, k, (V, s'), abstract) = ops'
       
       Invariant: 
       If  G0, G |- s' : G1  G1 |- V: type
       and  k = |local parameters in G|
       and  G is the context of local parameters
       and  abstract abstraction function
       then ops' is a list of all operators unifying with V[s']
	    (it contains constant and parameter cases)
    *)
    fun lowerSplitDest (G, k, (V as I.Root (I.Const c, _), s'), abstract, cases) =
          cases (c, G, I.ctxLength G , (V, s'), abstract)
(* k must change. It should consider all parameters in the context, and not just the local ones --cs *) 
(*          constCases (G, (V, s'), Index.lookup c, abstract, 
		      paramCases (G, (V, s'), I.ctxLength G, abstract, nil)) *)
      | lowerSplitDest (G, k, (I.Pi ((D, P), V), s'), abstract, cases) =
          let 
	    val D' = I.decSub (D, s')
	  in
	    lowerSplitDest (I.Decl (G, D'), k+1, (V, I.dot1 s'),
			    fn U => abstract (I.Lam (D', U)), cases)
  	  end



    fun abstractErrorLeft ((G, B), s) = 
      (TextIO.print "Cannot split left of parameters";
       raise MTPAbstract.Error "Cannot split left of parameters")

    fun abstractErrorRight ((G, B), s) = 
      (TextIO.print "Cannot split right of parameters";
       raise MTPAbstract.Error "Cannot split right of parameters")


    (* split (x:D, sc, B, abstract) = cases'

       Invariant :
       If   |- G ctx
       and  G |- B tags
       and  G |- D : L
       then sc is a function, which maps
	        Gp, Bp          (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p' 
		              (. |- G' = Gp, G'' ctx
	                       G'' contains only parameter declarations from G
	  	               G' |- B' tags
    		               G' |- s' : G
		               and p' holds iff (G', B') contains a parameter 
	 	    	     block independent of Gp, Bp)
        and  abstract is an abstraction function which maps
	       (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
	    to S'            (|- S' state)

       then cases' = (S1, ... Sn) are cases of the split
    *)
    fun split ((D as I.Dec (_, V), T), sc, abstract) = 
        let
	  fun split' (n, cases) = 
	    if n < 0 then 
	      let 
		val ((G', B'), s', (G0, B0), _) = sc (I.Null, I.Null)
					(* |- G' = parameter blocks of G  ctx*)
					(* G' |- B' tags *)
					(* G' |- s' : G *)
		fun abstract' U' = 
		  let 
					(* G' |- U' : V[s'] *)
					(* G' |- U.s' : G, V *)
		    val _ = TextIO.print ("[Abstraction in the base case: ...\n")
		    val _ = TextIO.print "U'.s' = "
		    val _ = inspect (I.Dot (I.Exp U', s'))
		    val _ = TextIO.print "\n" 
		    val _ = TextIO.print ("|G'| = " ^ (Int.toString (I.ctxLength G')) ^ "\n")
		    val ((G'', B''), s'') = MTPAbstract.abstractSub' ((G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))
		    val _ = TextIO.print "s'' = "
		    val _ = inspect s''
		    val _ = TextIO.print "\n" 
		    val Psi'' = aux (G'',B'')
		    val _ = TypeCheck.typeCheckCtx (F.makectx Psi'')
		    val _ = TextIO.print "\n|- Psi'' lfctx\n"

		    val Psi = aux (I.Decl (G0, D), I.Decl (B0, T))
		    val _ = TypeCheck.typeCheckCtx (F.makectx Psi)
		    val _ = TextIO.print "|- Psi lfctx\n"
		    val _ = FunTypeCheck.checkSub (Psi'', s'', Psi)
		    val _ = TextIO.print ("]\n")
		  in 
		    abstract ((G'', B''), s'')
		  end
	      in
		lowerSplitDest (G', 0, (V, s'), 
				abstract',
				constAndParamCases cases)
	      end
	    else
	      let
		val F.LabelDec (name, G1, G2) = F.labelLookup n
		val t = someEVars (I.Null, G1, I.id)
					(* . |- t : G1 *)
		val G2t = ctxSub (G2, t)
					(* . |- G2 [t] ctx *)
		val length = List.length G2
		val B2 = createTags (length , n)
					(* G2 [t] |- B2 tags *)
		val ((G', B'), s', (G0, B0), p) = sc (Names.ctxName (F.listToCtx G2t), B2)
					(* . |- G' ctx *)
					(* G' |- B' tags *)
					(* G' |- s : G = G0 *)
					(* G0 |- B0 tags *)

		(* abstract' U = S' 
		 
		   Invariant:
		   If   G' |- U' : V[s']
		   then |- S' state *)
		fun abstract' U' = 
					(* G' |- U' : V[s'] *)
		  if p then (TextIO.print "Cannot split right of parameters";
			     raise MTPAbstract.Error "Cannot split right of parameters")
		  else 
		    let 
					(* G' |- U.s' : G, V *)
					(* . |- t : G1 *)
		      val ((G'', B''), s'') = MTPAbstract.abstractSub (t, (G', B'), I.Dot (I.Exp U', s'), I.Decl (B0, T))

(*HERE*)
(*BUG: edit abstract so that it also collects EVars in the types of parameters
  then change abstractSub to abstractSub' and remove t
  -cs 
*)
					(* . |- G'' ctx *)
					(* G'' |- B'' tags *)
					(* G'' = G1'', G2', G2'' *)
					(* where G1'' |- G2' ctx, G2' is the abstracted parameter block *)
		    in 
		      abstract ((G'', B''), s'')
		    end
				
		val cases' = lowerSplitDest (G', 0, (V, s'), abstract',
					   metaCases (length, cases))
	      in
		split' (n - 1, cases')
	      end
	in
	  split' (F.labelSize () -1, nil)
	end
      

    (* occursIn (k, U) = B, 

       Invariant:
       If    U in nf 
       then  B iff k occurs in U
    *)
    fun occursInExp (k, I.Uni _) = false
      | occursInExp (k, I.Pi (DP, V)) = occursInDecP (k, DP) orelse occursInExp (k+1, V)
      | occursInExp (k, I.Root (C, S)) = occursInCon (k, C) orelse occursInSpine (k, S)
      | occursInExp (k, I.Lam (D,V)) = occursInDec (k, D) orelse occursInExp (k+1, V)
      (* no case for Redex, EVar, EClo *)

    and occursInCon (k, I.BVar (k')) = (k = k')
      | occursInCon (k, I.Const _) = false
      | occursInCon (k, I.Def _) = false
      | occursInCon (k, I.Skonst _) = false
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = false
      | occursInSpine (k, I.App (U, S)) = occursInExp (k, U) orelse occursInSpine (k, S)
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    fun isIndexInit k = false
    fun isIndexSucc (D, isIndex) k = occursInDec (k, D) orelse isIndex (k+1)  
    fun isIndexFail (D, isIndex) k = isIndex (k+1)


    (* abstractInit S ((G', B'), s') = S'
     
       Invariant:
       If   |- S = (n, (G, B), (IH, OH), d, O, H, F) state
       and  |- G' ctx
       and  G' |- B' tags
       and  G' |- s' : G
       then |- S' = (n, (G', B'), (IH, OH), d, O[s'], H[s'], F[s']) state
    *)
    fun abstractInit (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) ((G', B'), s') = 
          (if !Global.doubleCheck then TypeCheck.typeCheckCtx G' else ();
	  S.State (n, (G', B'), (IH, OH), d, S.orderSub (O, s'), 
		   map (fn (i, F') => (i, F.forSub (F', s'))) H, F.forSub (F, s')))


    (* abstractCont ((x:V, T), abstract) = abstract'
	      
       Invariant: 
       If   |- G ctx
       and  G |- V : type
       and  G |- B tags
       and  abstract is an abstraction function which maps
	            (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G, D)
		 to S'            (|- S' state)
       then abstract' is an abstraction function which maps
	            (Gn', Bn'), sn'  (|- Gn' ctx,  Gn' |- Bn' tags,  Gn' |- sn' : G)
		 to S'               (|- S' state)
    *)
    fun abstractCont ((D, T), abstract) ((G, B), s) =  
          abstract ((I.Decl (G, Whnf.normalizeDec (D, s)),
		     I.Decl (B, T)), I.dot1 s)


    fun makeAddressInit S k = (S, k)
    fun makeAddressCont makeAddress k = makeAddress (k+1)


    (* expand' ((G, B), isIndex, abstract, makeAddress) = (sc', ops')
	 
       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  isIndex (k) = B function s.t. B holds iff k index
       and  abstract is an abstraction function which maps
               (Gn, Bn), sn  (|- Gn ctx,  Gn |- Bn tags,  Gn |- sn : G)
	    to S'            (|- S' state)
       and  makeAddress, a function which calculates the index of the variable
            to be split
       then sc' is a function, which maps
               Gp, Bp         (. |- Gp ctx   Gp |- Bp tags)
            to (G', B'), s', (G, B), p' 
		              (. |- G' = Gp, G'' ctx
	                       G'' contains only parameter declarations from G
	  	               G' |- B' tags
    		               G' |- s' : G
		               and p' holds iff (G', B') contains a parameter 
	 	    	     block independent of Gp, Bp)
       and  ops' is a list of splitting operators
	     
       Optimization possible : 
         instead of reconstructin (G, B) as the result of sc, just take (G, B)
    *)
    fun expand' (GB as (I.Null, I.Null), isIndex,
		 abstract, 
		 makeAddress) =
        (fn (Gp, Bp) => ((Gp, Bp), I.Shift (I.ctxLength Gp), GB, false), nil)
      | expand' ((I.Decl (G, D), I.Decl (B, T as (S.Lemma (b, F.Ex _)))),
		 isIndex, abstract, makeAddress) = 
	let 
	  val (sc, ops) =
	    expand' ((G, B), isIndexSucc (D, isIndex), 
		     abstractCont ((D, T), abstract),
		     makeAddressCont makeAddress)
	  val I.Dec (xOpt, V) = D
	  fun sc' (Gp, Bp) = 
	    let 
	      val ((G', B'), s', (G0, B0), p') = sc (Gp, Bp)
	      val X = I.newEVar (G', I.EClo (V, s'))     (* G' |- X : V[s'] *)
	    in
	      ((G', B'), I.Dot (I.Exp (X), s'), (I.Decl (G0, D), I.Decl (B0, T)), p')        (* G' |- X.s' : G, D *)
	    end
	  val ops' = if not (isIndex 1) andalso b > 0
		       then 
			 (makeAddress 1, split ((D, T), sc, abstract))
			 :: ops
		     else ops
	in
	  (sc', ops')
	end
      | expand' ((I.Decl (G, D), I.Decl (B, T as (S.Lemma (b, F.All _)))), isIndex, 
		 abstract, 
		 makeAddress) = 
	let 
	  val (sc, ops) =
	    expand' ((G, B), isIndexSucc (D, isIndex),
		     abstractCont ((D, T), abstract),
		     makeAddressCont makeAddress)
	  val I.Dec (xOpt, V) = D
	  fun sc' (Gp, Bp) = 
	    let 
	      val ((G', B'), s', (G0, B0), p') = sc (Gp, Bp)
	      val X = I.newEVar (G', I.EClo (V, s'))
	    in
	      ((G', B'), I.Dot (I.Exp (X), s'), (I.Decl (G0, D), I.Decl (B0, T)), p')
	    end
	in
	  (sc', ops)
	end
      | expand' ((I.Decl (G, D), I.Decl (B, T as S.Parameter (SOME _))), isIndex, 
		 abstract, 
		 makeAddress) = 
	let 
	  val (sc, ops) =
	    expand' ((G, B), isIndexSucc (D, isIndex),
		     abstractErrorLeft,
		     makeAddressCont makeAddress)
	  val I.Dec (xOpt, V) = D
	  fun sc' (Gp, Bp) = 
	    let 
	      val ((G', B'), s', (G0, B0), _) = sc (Gp, Bp)
	      val _ = TextIO.print "*"
	    in
	      ((I.Decl (G', Names.decName (G', I.decSub (D, s'))), I.Decl (B', T)), 
	       I.dot1 s', (I.Decl (G0, D), I.Decl (B0, T)), true)
	    end
	  
	in
	  (sc', ops)
	end
    (* no case of (I.Decl (G, D), I.Decl (G, S.Parameter NONE)) *)
 


    (* expand (S) = ops'

       Invariant:
       If   |- S state
       then ops' is a list of all possiblie splitting operators
    *)
    fun expand (S0 as S.State (n, (G0, B0), _, _, _, _, _)) =
      let 
	val (_, ops) =
	  expand' ((G0, B0), isIndexInit, abstractInit S0, makeAddressInit S0)
      in
	ops
      end
    
    (* index (Op) = k
       
       Invariant:
       If   Op = (_, Sl) 
       then k = |Sl| 
    *)
    fun index (_, Sl) = List.length Sl


    (* isInActive (F) = B
       
       Invariant:
       B holds iff F is inactive
    *)
    fun isInActive (Active _) = false
      | isInActive (InActive) = true


    (* applicable (Op) = B'

       Invariant: 
       If   Op = (_, Sl) 
       then B' holds iff Sl does not contain inactive states
    *)
    fun applicable (_, Sl) = not (List.exists isInActive Sl)


    (* apply (Op) = Sl'
       
       Invariant:
       If   Op = (_, Sl) 
       then Sl' = Sl
       
       Side effect: If Sl contains inactive states, an exception is raised
    *)
    fun apply (_, Sl) = 
      map (fn (Active S) => S
	    | InActive => raise Error "Not applicable: leftover constraints")
      Sl
      
		
    (* menu (Op) = s'
       
       Invariant:
       If   Op = ((S, i), Sl)  and  S is named
       then s' is a string describing the operation in plain text

       (menu should hence be only called on operators which have 
        been calculated from a named state)
    *)
    fun menu (Op as ((S.State (n, (G, B), (IH, OH), d, O, H, F), i), Sl)) = 
	let 
	  fun active (nil, n) = n
	    | active (InActive :: L, n) = active (L, n)
	    | active ((Active _) :: L, n) = active (L, n+1)

	  fun inactive (nil, n) = n
	    | inactive (InActive :: L, n) = inactive (L, n+1)
	    | inactive ((Active _) :: L, n) = inactive (L, n)

	  fun indexToString 0 = "zero cases"
	    | indexToString 1 = "1 case"
	    | indexToString n = (Int.toString n) ^ " cases"

	  fun flagToString (_, 0) = ""
	    | flagToString (n, m) = " [active: " ^(Int.toString n) ^ 
		" inactive: " ^ (Int.toString m) ^ "]"
	in
	  "Splitting : " ^ Print.decToString (G, I.ctxDec (G, i)) ^
	  " (" ^ (indexToString (index Op)) ^ 
	   (flagToString (active (Sl, 0), inactive (Sl, 0))) ^ ")"
	end

  in
    val expand = expand
    val menu = menu
    val applicable = applicable
    val apply = apply
    val index = index

  end (* local *)
end;  (* functor Splitting *)
