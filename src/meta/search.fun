(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTPSearch (structure Global : GLOBAL
		   structure IntSyn' : INTSYN
		   structure Abstract : ABSTRACT
		     sharing Abstract.IntSyn = IntSyn'
		   structure MTPGlobal : MTPGLOBAL
		   structure StateSyn' : STATESYN
		   sharing StateSyn'.FunSyn.IntSyn = IntSyn'
		   structure CompSyn' : COMPSYN
		   sharing CompSyn'.IntSyn = IntSyn'
		   structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
		   structure Unify : UNIFY
		   sharing Unify.IntSyn = IntSyn'
		   (*
		structure Assign : ASSIGN
sharing Assign.IntSyn = IntSyn'
		    *)
		   structure Index : INDEX
		   sharing Index.IntSyn = IntSyn'
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
  : MTPSEARCH =
struct

  structure IntSyn = IntSyn'
  structure StateSyn = StateSyn'
  structure CompSyn = CompSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure C = CompSyn

      
    (* isInstantiated (V) = SOME(cid) or NONE
       where cid is the type family of the atomic target type of V,
       NONE if V is a kind or object or have variable type.
    *)
    fun isInstantiated (I.Root (I.Const(cid), _)) = true
      | isInstantiated (I.Pi(_, V)) = isInstantiated V
      | isInstantiated (I.Root (I.Def(cid), _)) = true
      | isInstantiated (I.Redex (V, S)) = isInstantiated V
      | isInstantiated (I.Lam (_, V)) = isInstantiated V
      | isInstantiated (I.EVar (ref (SOME(V)),_,_,_)) = isInstantiated V
      | isInstantiated (I.EClo (V, s)) = isInstantiated V
      | isInstantiated _ = false
      

    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun exists' (I.Null) = false
	      | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
	in
	  exists' K
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
      | occursInExpW (r, (I.EVar (r' , _, V', _), s)) = 
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
      | nonIndex (r, I.EVar (_, _, V, _) :: GE) = 
          (not (occursInExp (r, (V, I.id)))) andalso nonIndex (r, GE)

    (* select (GE, (V, s), acc) = acc'

       Invariant:
    *)
    (* Efficiency: repeated whnf for every subterm in Vs!!! *)
    fun selectEVar (nil) = nil
      | selectEVar ((X as I.EVar (r, _, _, nil)) :: GE) = 
        let 
	  val Xs = selectEVar (GE)
	in
	  if nonIndex (r, Xs) then Xs @ [X]
	  else Xs
	end
      | selectEVar ((X as I.EVar (r, _, _, Constr)) :: GE) =  (* Constraint case *)
        let 
	  val Xs = selectEVar (GE)
	in
	  if nonIndex (r, Xs) then X :: Xs
	  else Xs
	end


    (* pruneCtx (G, n) = G'

       Invariant:
       If   |- G ctx
       and  G = G0, G1
       and  |G1| = n
       then |- G' = G0 ctx
    *)
    fun pruneCtx (G, 0) = G
      | pruneCtx (I.Decl (G, _), n) = pruneCtx (G, n-1)

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
  fun solve (max, depth, (C.Atom p, s), dp, sc, acck) = matchAtom (max, depth, (p,s), dp, sc, acck)
    | solve (max, depth, (C.Impl (r, A, cid, g), s), C.DProg (G, dPool), sc, acck) =
       let
	 val D' = I.Dec (NONE, I.EClo (A, s))
       in
	 solve (max, depth+1, (g, I.dot1 s), 
		C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, cid))),
		(fn (M, acck') => sc (I.Lam (D', M), acck')), acck)
       end
    | solve (max, depth, (C.All (D, g), s), C.DProg (G, dPool), sc, acck) =
       let
	 val D' = I.decSub (D, s)
       in
	 solve (max, depth+1, (g, I.dot1 s), 
		C.DProg (I.Decl (G, D'), I.Decl (dPool, NONE)),
		(fn (M, acck') => sc (I.Lam (D', M), acck')), acck)
       end

  (* rsolve (max, depth, (p,s'), (r,s), (G,dPool), sc, (acc, k)) = ()
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
  and rSolve (max, depth, ps', (C.Eq Q, s), C.DProg (G, dPool), sc, acck as (acc, k)) =
      if Unify.unifiable (G, ps', (Q, s))
	then sc (I.Nil, acck)
      else acc
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)
    (*
    | rSolve (max, ps', (C.Assign (Q, ag), s), Dp, sc, acck as (acc, k)) =
        ((Assign.assign (ps', (Q, s));
	  aSolve ((ag, s), Dp, (fn () => sc (I.Nil, acck)) , acc))
	  handle Unify.Unify _ => acc
	       | Assign.Assign _ => acc)
    *)
    | rSolve (max, depth, ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc, acck) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (max, depth, ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn (S, acck') => solve (max, depth, (g, s), dp,
					 (fn (M, acck'') => sc (I.App (M, S), acck'')), acck')), acck)

      end
    | rSolve (max, depth, ps', (C.In (r, A, g), s), dp as C.DProg (G, dPool), sc, acck) =
      let
					(* G |- g goal *)
					(* G |- A : type *)
					(* G, A |- r resgoal *)
					(* G0, Gl  |- s : G *)
	val G0 = pruneCtx (G, depth)
	val dPool0 = pruneCtx (dPool, depth)
	val w = I.Shift (depth)		(* G0, Gl  |- w : G0 *)
	val iw = Whnf.invert w
					(* G0 |- iw : G0, Gl *)
	val s' = I.comp (s, iw)
					(* G0 |- w : G *)
	val X = I.newEVar (G0, I.EClo(A, s'))
					(* G0 |- X : A[s'] *)
	val X' = I.EClo (X, w)
					(* G0, Gl |- X' : A[s'][w] = A[s] *)
      in
	rSolve (max, depth, ps', (r, I.Dot (I.Exp (X'), s)), dp,
		(fn (S, acck') => 
		   if isInstantiated X then sc (I.App (X', S), acck')
		   else  solve (max, 0, (g, s'), C.DProg (G0, dPool0),
				(fn (M, acck'' as (acc'', _)) => 
				 ((Unify.unify (G0, (X, I.id), (M, I.id)); 
				  sc (I.App (I.EClo (M, w), S), acck'')) 
				 handle Unify.Unify _ => acc'')), acck')), acck)

(*
		   case Y
		     of I.EVar (ref NONE, _, _, _) => 
		          solve (0, (g, s'), dp,
				 (fn (M, acck'') => sc (I.App (I.EClo (M, w), S), acck'')), acck')
		      | I.EVar (ref (SOME _), _, _, _) => sc (I.App (X', S), acck')), acck)
*)
(*		       (searchEx' k' (selectEVar (Abstract.collectEVars (G, (X', I.id), nil)),
				      fn _ => (sc (I.App (X', S), acck'); ())))), acck)
*)
(*    | rSolve (depth, ps', (C.In (r, A, g), s), dp as C.DProg (G, dPool), sc, acck) =
      let
	val Gpruned = pruneCtx (G, depth)
	val w = I.Shift (depth)		(* G |- w : Gpruned *)
	val X = I.EClo (I.newEVar (Gpruned, I.EClo(A, s)), w)
      in
	rSolve (depth, ps', (r, I.Dot (I.Exp (X), s)), dp,
		(fn (S, acck' as (_, k')) => 
		   (searchEx' k' (selectEVar (Abstract.collectEVars (G, (X, I.id), nil)),
				     fn _ => (sc (I.App (X, S), acck'); ())))), acck)
*)
(*		(fn (S, acck') => solve (depth, (g, s), dp,
					 (fn (M, acck'') => ((Unify.unify (G, (X, I.id), (M, I.id));
							     (* why doesn't it always succeed?
							        --cs *)
							     sc (I.App (M, S), acck''))
							     handle Unify.Unify _ => [])), 
					 acck')), acck)
*)      end
    | rSolve (max, depth, ps', (C.Exists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
	  val X = I.newEVar (G, I.EClo (A, s))
	in
	  rSolve (max, depth, ps', (r, I.Dot (I.Exp (X), s)), dp,
		  (fn (S, acck') => sc (I.App (X, S), acck')), acck)
	end
    | rSolve (max, depth, ps', (C.Exists' (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc, acck) =
        let
	  val X = I.newEVar (G, I.EClo (A, s))
	in
	  rSolve (max, depth, ps', (r, I.Dot (I.Exp (X), s)), dp,
		  (fn (S, acck') => sc (S, acck')), acck)
	end

  (* aSolve ... *)
  and aSolve ((C.Trivial, s), dp, sc, acc) = sc ()
    (* Fri Jan 15 16:04:39 1999 -fp,cs
    | aSolve ((C.Unify(I.Eqn(e1, e2), ag), s), dp, sc, acc) =
      ((Unify.unify ((e1, s), (e2, s));
        aSolve ((ag, s), dp, sc, acc))
       handle Unify.Unify _ => acc)
     *)

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
  and matchAtom (0, _, _, _, _, (acc, k)) = acc
    | matchAtom (max, depth, 
		 ps' as (I.Root (I.Const cid, _), _), 
		 dp as C.DProg (G, dPool), sc, (acc, k)) =
      let
	fun matchSig acc' =
	    let
	      fun matchSig' (nil, acc'') = acc''
		| matchSig' (H ::sgn', acc'') =
		  let
		    val cid' = (case H 
				  of I.Const cid => cid
				   | I.Skonst cid => cid)
				  
		    val C.SClause(r) = C.sProgLookup cid'
		    val acc''' = Trail.trail
		                 (fn () =>
				    rSolve (max-1, depth, ps', (r, I.id), dp,
					    (fn (S, acck') => sc (I.Root (H, S),
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
			    rSolve (max-1,depth, ps', (r, I.comp (s, I.Shift n)), dp,
				    (fn (S, acck') => sc (I.Root (I.BVar n, S),
							  acck')), (acc', k-1)))
	      in
		matchDProg (dPool', n+1, acc'')
	      end
	    else matchDProg (dPool', n+1, acc')
	  | matchDProg (I.Decl (dPool', NONE), n, acc') =
	      matchDProg (dPool', n+1, acc')
      in
	(* if k < 0 then acc else *) matchDProg (dPool, 1, acc)
      end


    (* searchEx' max (GE, sc) = acc'

       Invariant: 
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    and searchEx' max (nil, sc) = [sc max]
        (* Possible optimization: 
	   Check if there are still variables left over
	*)
      | searchEx' max ((X as I.EVar (r, G, V, _)) :: GE, sc) = 
	  solve (max, 0, (Compile.compileGoal (G, V), I.id), 
		 Compile.compileCtx false G, 
		 (fn (U', (acc', _)) => (Unify.unify (G, (X, I.id), (U', I.id));
					 searchEx' max (GE, sc)) handle Unify.Unify _ => acc'),
		 (nil, max))

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and 
	 traversing all possible numbers up to MTPGlobal.maxLevel
    *)
    fun deepen depth f P =
	let 
	  fun deepen' (level, acc) = 
	    if level > depth then acc
	    else (if !Global.chatter > 5 then print "#" else (); 
		    deepen' (level+1, f level P))
	in
	  deepen' (1, nil)
	end

    (* searchEx (G, GE, (V, s), sc) = acc'
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
	 where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
	 been instantiated
       then acc' is a list containing the one result from executing the success continuation 
	 All EVar's got instantiated with the smallest possible terms.
    *)    

    fun searchEx (it, depth) (GE, sc) = 
      (if !Global.chatter > 5 then print "[Search: " else ();  
	 deepen depth searchEx' (selectEVar (GE), 
			   fn max => (if !Global.chatter > 5 then print "OK]\n" else ();
					 let
					   val GE' = foldr (fn (X as I.EVar (_, G, _, _), L) => 
							    Abstract.collectEVars (G, (X, I.id), L)) nil GE
					   val gE' = List.length GE'
(*					   val _ = if !Global.chatter > 4 then TextIO.print (Int.toString gE' ^ " remaining EVars\n") else ()  *)
					 in
					   if gE' > 0 then  
					     if it > 0 then searchEx (it-1, 1) (GE', sc) 
					     else ()
					   else sc max
					   (* warning: iterative deepening depth is not propably updated. 
					      possible that it runs into an endless loop ? *)
					 end)); 
	 if !Global.chatter > 5 then print "FAIL]\n" else ();
	   ())
(*

    fun searchEx (it, depth) (GE, sc) = 
      (if !Global.chatter > 5 then print "[Search: " else ();  
	 deepen depth searchEx' (selectEVar (GE), 
				 fn max => (if !Global.chatter > 5 then print "OK]\n" else ();
					      sc max)); 
	 if !Global.chatter > 5 then print "FAIL]\n" else ())
	
*)  
    fun search (GE, sc) = searchEx (1, !MTPGlobal.maxFill) (GE, sc)

(*    (* searchAll' (GE, acc, sc) = acc'

       Invariant: 
       If   GE is a list of EVars to be instantiated
       and  acc is list of already collected results of the success continuation
       then acc' is an extension of acc', containing the results of sc
	 after trying all combinations of instantiations of EVars in GE
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)

    fun searchAll' (nil, acc, sc) = sc (acc)
      | searchAll' (I.EVar (r, G, V, _) :: GE, acc, sc) = 
	  solve ((Compile.compileGoal (G, V), I.id), 
		 Compile.compileCtx false G, 
		 (fn (U', (acc', _)) => (Trail.instantiateEVar (r, U'); 
					 searchAll' (GE, acc', sc))),
		 (acc, !MTPGlobal.maxFill))

    (* searchAll (G, GE, (V, s), sc) = acc'
     
       Invariant:
       If   G |- s : G'   G' |- V : level
       and  GE is a list of EVars contained in V[s]
	 where G |- X : VX
       and  sc is a function to be executed after all non-index variables have
	 been instantiated
       then acc' is a list of results from executing the success continuation 
    *)
    fun searchAll (G, GE, Vs, sc) =
          searchAll' (selectEVar (GE, Vs, nil), nil, sc)
*)

  in 
    val searchEx = search
  end (* local ... *)

end; (* functor Search *)
 
