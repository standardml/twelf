(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor AbsMachine (structure IntSyn' : INTSYN
		    structure CompSyn' : COMPSYN
		      sharing CompSyn'.IntSyn = IntSyn'
		    structure Unify : UNIFY
		      sharing Unify.IntSyn = IntSyn'
		    (*
                    structure Assign : ASSIGN
		      sharing Assign.IntSyn = IntSyn'
		    *)

		    structure Index : INDEX
		      sharing Index.IntSyn = IntSyn'
		    (* CPrint currently unused *)
		    structure CPrint : CPRINT 
                      sharing CPrint.IntSyn = IntSyn'
                      sharing CPrint.CompSyn = CompSyn'
		    structure Names : NAMES 
                      sharing Names.IntSyn = IntSyn'
		    structure CSManager : CS_MANAGER
		      sharing CSManager.IntSyn = IntSyn')
  : ABSMACHINE =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    structure I = IntSyn
    structure C = CompSyn
  in

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

  fun cidFromHead (I.Const a) = a
    | cidFromHead (I.Def a) = a

  fun eqHead (I.Const a, I.Const a') = a = a'
    | eqHead (I.Def a, I.Def a') = a = a'
    | eqHead _ = false
                              
  (* solve ((g, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve ((C.Atom(p), s), dp, sc) = matchAtom ((p,s), dp, sc)
    | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.Dec(NONE, I.EClo(A,s))
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, SOME(r, s, Ha))),
	       (fn M => sc (I.Lam (D', M))))
      end
    | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
	val D' = I.decSub (D, s)
      in
	solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, NONE)),
	       (fn M => sc (I.Lam (D', M))))
      end

  (* rsolve ((p,s'), (r,s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =
     (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
	then sc I.Nil			(* call success continuation *)
      else ()				(* fail *)
	)
    (* Fri Jan 15 14:29:28 1999 -fp,cs
    | rSolve (ps', (Assign(Q, ag), s), dp, sc) = 
     (if Assign.assignable (ps', (Q, s)) then
	aSolve ((ag, s), dp, (fn () => sc I.Nil))
      else ())
    *)
    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
	(* is this EVar redundant? -fp *)
	val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => solve ((g, s), dp,
				(fn M => sc (I.App (M, S))))))
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
		(fn S => sc (I.App(X,S))))
      end
    (*
    | rSolve (ps', (C.Exists'(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
	val X = I.newEVar (G, I.EClo (A,s))
      in
	rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, sc)
   	          (* we don't increase the proof term here! *)
      end
     *)

  (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal then
       sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *)
  and aSolve ((C.Trivial, s), dp, sc) = sc ()
    (* Fri Jan 15 14:31:20 1999 -fp,cs
    | aSolve ((Unify(I.Eqn(e1, e2), ag), s), dp, sc) =
    (if Unify.unifiable ((e1, s), (e2, s)) then aSolve ((ag, s), dp, sc)
     else ())
    *)

  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
	   try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
	fun matchSig nil = ()	(* return indicates failure *)
	  | matchSig (Hc::sgn') =
	    let
	      val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
	    in
	      (* trail to undo EVar instantiations *)
	      CSManager.trail (fn () =>
			       rSolve (ps', (r, I.id), dp,
				       (fn S => sc (I.Root(Hc, S))))) ;
	      matchSig sgn'
	    end

        (* matchDProg (dPool, k) = ()
	   where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
	fun matchDProg (I.Null, _) =
	    (* dynamic program exhausted, try signature *)
	    matchSig (Index.lookup (cidFromHead Ha)) 
	  | matchDProg (I.Decl (dPool', SOME(r, s, Ha')), k) =
	    if eqHead (Ha, Ha')
	      then (* trail to undo EVar instantiations *)
		    (CSManager.trail (fn () =>
		                      rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
				              (fn S => sc (I.Root(I.BVar(k), S))))) ;
		     matchDProg (dPool', k+1))
	    else matchDProg (dPool', k+1)
	  | matchDProg (I.Decl (dPool', NONE), k) =
	      matchDProg (dPool', k+1)
        fun matchConstraint (solve, try) =
              let
                val succeeded =
                  CSManager.trail
                    (fn () =>
                       case (solve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc (U) ; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (solve, try+1)
                else ()
              end      
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
           | _ => matchDProg (dPool, 1)
      end
  end (* local ... *)

end; (* functor AbsMachine *)
