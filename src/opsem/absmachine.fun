(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Larry Greenfield *)

functor AbsMachine (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    (*
                    structure Assign : ASSIGN
		      sharing Assign.IntSyn = IntSyn'
		    *)
		    structure Trail : TRAIL
		      sharing Trail.IntSyn = IntSyn'
		    (* CPrint currently unused *)
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
		    structure Names : NAMES 
                      sharing Names.IntSyn = IntSyn')
  : ABSMACHINE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    open CompSyn
  in

    fun showTrace s = 
      if (!Global.chatter) >= 5 then
	TextIO.print (s ())
      else
	()

  (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
  *)

  (* solve ((g, s), dProg, sc) => ()
     Invariants:
       dProg = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dProg
              any effect  sc M  might have
  *)
  fun solve ((Atom(p), s), dProg, sc) = matchAtom ((p,s), dProg, sc)
    | solve ((Impl(r, A, a, g), s), (G, dPool), sc) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve ((g, I.dot1 s), (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, a))),
	       (fn M => sc (I.Lam (D', M))))
      end
    | solve ((All(D, g), s), (G, dPool), sc) =
      let
	val D' = I.decSub (D, s)
      in
	solve ((g, I.dot1 s), (I.Decl(G, D'), I.Decl(dPool, NONE)),
	       (fn M => sc (I.Lam (D', M))))
      end

  (* rsolve ((p,s'), (r,s), dProg, sc) = ()
     Invariants:
       dProg = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dProg
              any effect  sc S  might have
  *)
  and rSolve (ps', (Eq(Q), s), (G, dPool), sc) =
     (showTrace (fn () => "unifying...\n");
      if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	then sc I.Nil			(* call success continuation *)
      else ()				(* fail *)
	)
    (* Fri Jan 15 14:29:28 1999 -fp,cs
    | rSolve (ps', (Assign(Q, ag), s), dProg, sc) = 
     (showTrace (fn () => "assigning...\n");
      if Assign.assignable (ps', (Q, s)) then
	aSolve ((ag, s), dProg, (fn () => sc I.Nil))
      else ())
    *)
    | rSolve (ps', (And(r, A, g), s), dProg as (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dProg,
		(fn S => solve ((g, s), dProg,
				(fn M => sc (I.App (M, S))))))
      end
    | rSolve (ps', (Exists(I.Dec(_,A), r), s), dProg as (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))

	val _ = showTrace (fn () => "introducing existential variable...\n")
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dProg,
		(fn S => sc (I.App(X,S))))
      end
    | rSolve (ps', (Exists'(I.Dec(_,A), r), s), dProg as (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))

	val _ = showTrace (fn () => "introducing existential' variable...\n")
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dProg, sc)
   	          (* we don't increase the proof term here! *)
      end

  (* aSolve ((ag, s), dProg, sc) = ()
     Invariants:
       dProg = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal then
       sc () is evaluated
     Effects: instantiation of EVars in ag[s], dProg and sc () *)
  and aSolve ((Trivial, s), dProg, sc) = sc ()
    (* Fri Jan 15 14:31:20 1999 -fp,cs
    | aSolve ((Unify(I.Eqn(e1, e2), ag), s), dProg, sc) =
    (showTrace (fn () => "unifying...\n");
     if Unify.unifiable ((e1, s), (e2, s)) then aSolve ((ag, s), dProg, sc)
     else ())
    *)

  (* matchatom ((p, s), dProg, sc) => ()
     Invariants:
       dProg = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dProg
              any effect  sc M  might have

     This first tries the local assumptions in dProg then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(I.Const(a),_),_), dProg as (G,dPool), sc) =
      let
	val _ = showTrace 
	          (fn () => "matching...\n")

        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig (c::sgn') =
	    let
	      val SClause(r) = sProgLookup c
	    in
	      (* trail to undo EVar instantiations *)
	      Trail.trail (fn () =>
			   rSolve (ps', (r, I.id), dProg,
				   (fn S => sc (I.Root(I.Const(c), S))))) ;
	      showTrace (fn () => "signature backtracking...\n");
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    matchSig (Index.lookup a) 
	  | matchDProg (I.Decl (dPool', SOME(r, s, a')), k) =
	    if a = a'
	      then (* trail to undo EVar instantiations *)
		    (Trail.trail (fn () =>
		                rSolve (ps', (r, I.comp(s, I.Shift(k))), dProg,
				  (fn S => sc (I.Root(I.BVar(k), S))))) ;
		     showTrace (fn () => "dprog backtracking...\n");
		     matchDProg (dPool', k+1))
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', NONE), k) =
	      matchDProg (dPool', k+1)
      in
	matchDProg (dPool, 1)
      end
  end (* local ... *)

end; (* functor AbsMachine *)
