(* Search (based on abstract machine ) *)
(* Author: Carsten Schuermann *)

functor Search (structure IntSyn' : INTSYN
		structure MetaGlobal : METAGLOBAL
		structure MetaSyn' : METASYN
		sharing MetaSyn'.IntSyn = IntSyn'
		structure CompSyn' : COMPSYN
		sharing CompSyn'.IntSyn = IntSyn'
		structure Whnf : WHNF
		sharing Whnf.IntSyn = IntSyn'
		structure Unify : UNIFY
		sharing Unify.IntSyn = IntSyn'
		structure Assign : ASSIGN
		sharing Assign.IntSyn = IntSyn'
		structure Compile : COMPILE
		sharing Compile.IntSyn = IntSyn'
		sharing Compile.CompSyn = CompSyn'
		structure Trail : TRAIL
		sharing Trail.IntSyn = IntSyn'
		structure CPrint : CPRINT
		sharing CPrint.IntSyn = IntSyn'
		sharing CPrint.CompSyn = CompSyn'
		structure Print : PRINT
		sharing Print.IntSyn = IntSyn'
		structure Names : NAMES 
		sharing Names.IntSyn = IntSyn')
  : SEARCH =
struct

  structure IntSyn = IntSyn'
  structure MetaSyn = MetaSyn'
  structure CompSyn = CompSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = MetaSyn
    structure C = CompSyn


  (* solve ((g,s), (G,dPool), sc, (acc, k)) => ()
     Invariants:
       G |- s : G'
       G' |- g :: goal
       G ~ dPool  (context G matches dPool)
       acc is the accumulator of results
       and k is the max search depth limit 
	   (used in the existential case for iterative deepening,
	    used in the universal case for max search depth)
       if  G |- M :: g[s] then G |- sc :: g[s] => Answer, Answer closed
  *)
  fun solve ((C.Atom p, s), DProg, sc, acck) = matchAtom ((p,s), DProg, sc, acck)
    | solve ((C.Impl (r, A, cid, g), s), (G, dPool), sc, acck) =
       let
	 val D' = I.Dec (NONE, I.EClo (A, s))
       in
	 solve ((g, I.dot1 s), 
		(I.Decl(G, D'), I.Decl (dPool, SOME(r, s, cid))),
		(fn (M, acck') => sc (I.Lam (D', M), acck')), acck)
       end
    | solve ((C.All (D, g), s), (G, dPool), sc, acck) =
       let
	 val D' = I.decSub (D, s)
       in
	 solve ((g, I.dot1 s), 
		(I.Decl (G, D'), I.Decl (dPool, NONE)),
		(fn (M, acck') => sc (I.Lam (D', M), acck')), acck)
       end

  (* rsolve ((p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
     Invariants:
       G |- s : G'
       G' |- r :: resgoal
       G |- s' : G''
       G'' |- p :: atom
       G ~ dPool
       acc is the accumulator of results
       and k is the max search depth limit 
	   (used in the existential case for iterative deepening,
	    used in the universal case for max search depth)
       if G |- S :: r[s] then G |- sc : (r >> p[s']) => Answer
  *)
  and rSolve (ps', (C.Eq Q, s), DProg, sc, acck as (acc, k)) =
      if Unify.unifiable (ps', (Q, s))
	then sc (I.Nil, acck)
      else acc
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    | rSolve (ps', (C.Assign (Q, ag), s), DProg, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
	  aSolve ((ag, s), DProg, (fn () => sc (I.Nil, acck)) , acc))
	  handle Unify.Unify _ => acc
	       | Assign.Assign _ => acc)
    | rSolve (ps', (C.And (r, A, g), s), DProg, sc, acck) =
      let
	val X = I.newEVar (I.EClo(A, s))
      in
	rSolve (ps', (r, I.Dot (I.Exp (X, A), s)), DProg,
		(fn (S, acck') => solve ((g, s), DProg,
					 (fn (M, acck'') => sc (I.App (M, S), acck'')), 
					 acck')), acck)
      end
    | rSolve (ps', (C.Exists (I.Dec (_, A), r), s), DProg, sc, acck) =
        let
	  val X = I.newEVar (I.EClo (A, s))
	in
	  rSolve (ps', (r, I.Dot (I.Exp (X, A), s)), DProg,
		  (fn (S, acck') => sc (I.App (X, S), acck')), acck)
	end
    | rSolve (ps', (C.Exists' (I.Dec (_, A), r), s), DProg, sc, acck) =
        let
	  val X = I.newEVar (I.EClo (A, s))
	in
	  rSolve (ps', (r, I.Dot (I.Exp (X, A), s)), DProg,
		  (fn (S, acck') => sc (S, acck')), acck)
	end

  (* aSolve ... *)
  and aSolve ((C.Trivial, s), DProg, sc, acc) = sc ()
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), DProg, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), DProg, sc, acc))
       handle Unify.Unify _ => acc)

  (* matchatom ((p, s), (G, dPool), sc, (acc, k)) => ()
     G |- s : G'
     G' |- p :: atom
     G ~ dPool
     acc is the accumulator of results
     and k is the max search depth limit 
         (used in the existential case for iterative deepening,
          used in the universal case for max search depth)
     if G |- M :: p[s] then G |- sc :: p[s] => Answer
  *)
  and matchAtom (ps' as (I.Root (I.Const cid, _), _), 
		 dProg as (G, dPool), sc, (acc, k)) =
      let
	fun matchSig acc' =
	    let
	      fun matchSig' (nil, acc'') = acc''
		| matchSig' (cid'::sgn', acc'') =
		  let
		    val C.SClause(r) = C.sProgLookup cid'
		    val acc''' = Trail.trail
		                 (fn () =>
				    rSolve (ps', (r, I.id), dProg,
					    (fn (S, acck') => sc (I.Root (I.Const cid', S),
								  acck')), (acc'', k-1)))
		  in
		    matchSig' (sgn', acc''')
		  end
	    in
	      matchSig' (Index.lookup cid, acc')
	    end

	fun matchDProg (I.Null, _, acc') = matchSig acc'
	  | matchDProg (I.Decl (dPool', SOME (r, s, cid')), n, acc') =
	    if cid = cid' then
	      let
		val acc'' = Trail.trail (fn () =>
			    rSolve (ps', (r, I.comp (s, I.Shift n)), dProg,
				    (fn (S, acck') => sc (I.Root (I.BVar n, S),
							  acck')), (acc', k-1))) 
	      in
		matchDProg (dPool', n+1, acc'')
	      end
	    else matchDProg (dPool', n+1, acc')
	  | matchDProg (I.Decl (dPool', NONE), n, acc') =
	      matchDProg (dPool', n+1, acc')
      in
	if k < 0 then acc else matchDProg (dPool, 1, acc)
      end


    (* occursInExp (r, (U, s)) = B, 

       Invariant:
       If    G |- s : G1   G1 |- U : V 
       then  B holds iff r occurs in (the normal form of) U
    *)
    fun occursInExp (r, Vs) = occursInExpW (r, Whnf.whnf Vs)

    and occursInExpW (r, (I.Uni _, _)) = false
      | occursInExpW (r, (I.Pi ((D, _), V), s)) = 
          occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s))
      | occursInExpW (r, (I.Root (_, S), s)) = occursInSpine (r, (S, s))
      | occursInExpW (r, (I.Lam (D, V), s)) = 
	  occursInDec (r, (D, s)) orelse occursInExp (r, (V, I.dot1 s))
      | occursInExpW (r, (I.EVar (r' ,V', _), s)) = 
          (r = r') orelse occursInExp (r, (V', s))

    and occursInSpine (_, (I.Nil, _)) = false
      | occursInSpine (r, (I.SClo (S, s'), s)) = 
          occursInSpine (r, (S, I.comp (s', s)))
      | occursInSpine (r, (I.App (U, S), s)) = 
	  occursInExp (r, (U, s)) orelse occursInSpine (r, (S, s))

    and occursInDec (r, (I.Dec (_, V), s)) = occursInExp (r, (V, s))

    (* nonIndex (r, GE) = B
     
       Invariant: 
       B hold iff
        r does not occur in any type of EVars in GE
    *)
    fun nonIndex (_, nil) = true
      | nonIndex (r, (G, I.EVar (_, V, _)) :: GE) = 
          (not (occursInExp (r, (V, I.id)))) andalso nonIndex (r, GE)

    (* select (GE, (V, s), acc) = acc'

       Invariant:
       If   GE is a list of (G, X) (EVars and their contexts) 
       and  G |- s : G'   G' |- V : L
       then acc' is a list of EVars (G', X') s.t.
	 (0) it extends acc'
	 (1) (G', X') occurs in V[s]
	 (2) (G', X') is not an index Variable to any (G, X) in acc'.
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)

    fun selectEVar (nil, _, acc) = acc
      | selectEVar ((GX as (G, I.EVar (r, _, _))) :: GE, Vs, acc) = 
          if occursInExp (r, Vs) andalso nonIndex (r, acc) then
	    selectEVar (GE, Vs, GX :: acc)
	  else selectEVar (GE, Vs, acc)


    (* lowerEVar (G, X) = (G', X') 
       
       Invariant 
       If    G |- X : {V1} .. {Vn} a S
       then  G' = G, V1 .. Vn
       and   G' |- X' : a S
    *)
    (* Efficiency improvement: do not create intermediate EVars -fp *)
    fun lowerEVar (GX as (G, X as I.EVar (r, V, C))) = 
          lowerEVar' (G, X, Whnf.whnf (V, I.id), C)
    and lowerEVar' (G, X, (V as I.Root _, s (* = id *)), C) = 
          (G, X)
      | lowerEVar' (G, X as I.EVar (r, _, _), (I.Pi ((D, _), V), s), C) =
	let
	  val D' = I.decSub (D, s)
	  val X' = I.newEVar (I.EClo (V, I.dot1 s))
	in
	  (r := SOME (I.Lam (D', X')); lowerEVar (I.Decl (G, D'), X'))
	end

    (* lower GE = GE'

       Invariant: 
       For every (G, X) in GE there exisits a (G', X') s.t.
       if    G |- X : {V1} .. {Vn} a S
       then  G' = G, V1 .. Vn
       and   G' |- X' : a S
    *)
    fun lower nil = nil
      | lower (GX :: GE) = (lowerEVar GX) :: (lower GE)
 

    exception Success of M.State
    (* searchEx' max (GE, sc) = acc'

       Invariant: 
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found GE is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    fun searchEx' max (nil, sc) = raise Success (sc ())   
        (* Possible optimization: 
	   Check if there are still variables left over
	*)
      | searchEx' max ((G, I.EVar (r, V, _)) :: GE, sc) = 
	  solve ((Compile.compileGoal (G, V), I.id), 
		 Compile.compileCtx false G, 
		 (fn (U', (acc', _)) => (Trail.instantiateEVar (r, U'); 
					 searchEx' max (GE, sc))),
		 (nil, max))

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MetaGlobal.maxLevel
       then R' is the result of applying f to P and 
	 traversing all possible numbers up to MetaGlobal.maxLevel
    *)
    fun deepen f P =
	let 
	  fun deepen' (level, acc) = 
	    if level > (!MetaGlobal.maxFill) then acc
	    else (if !Global.chatter > 5 then print "#" else (); 
		    deepen' (level+1, f level P))
	in
	  deepen' (1, nil)
	end

    (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of (G, X) EVars contained in V[s]
	 where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
	 been instantiated
       then acc' is a list containing the one result from executing the success continuation 
	 All EVar's got instantiated with the smallest possible terms.
    *)    
    fun searchEx (G, GE, Vs, sc) = 
        ((if !Global.chatter > 5 then print "[Search: " else ();  
	    deepen searchEx' (selectEVar ((lower GE), Vs, nil), sc); 
	    if !Global.chatter > 5 then print "FAIL]\n" else ();
	      raise Error "No object found")
	    handle Success S => (if !Global.chatter > 5 then 
				   print "OK]\n" else (); [S]))
	  
    (* searchAll' (GE, acc, sc) = acc'

       Invariant: 
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
	 after trying all comibinations of instantiations of EVars in GE
    *)
    (* Shared contexts in GEVars may recompiled many times *)

    fun searchAll' (nil, acc, sc) = sc () :: acc
      | searchAll' ((G, I.EVar (r, V, _)) :: GE, acc, sc) = 
	  solve ((Compile.compileGoal (G, V), I.id), 
		 Compile.compileCtx false G, 
		 (fn (U', (acc', _)) => (Trail.instantiateEVar (r, U'); 
					 searchAll' (GE, acc', sc))),
		 (acc, !MetaGlobal.maxFill))

    (* searchAll (G, GE, (V, s), sc) = acc'
     
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of (G, X) EVars contained in V[s]
	 where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
	 been instantiated
       then acc' is a list of results from executing the success continuation 
    *)
    fun searchAll (G, GE, Vs, sc) =
          searchAll' (selectEVar (lower GE, Vs, nil), nil, sc)


  in 
    val searchEx = searchEx
    val searchAll = searchAll
  end (* local ... *)

end; (* functor Search *)
 
