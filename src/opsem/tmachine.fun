(* Abstract Machine for Tracing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor TMachine ((*! structure IntSyn' : INTSYN !*)
                  (*! structure CompSyn' : COMPSYN !*)
                  (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                  structure Unify : UNIFY
                  (*! sharing Unify.IntSyn = IntSyn' !*)

                  structure Assign : ASSIGN
                  (*! sharing Assign.IntSyn = IntSyn' !*)

                  structure Index : INDEX
                  (*! sharing Index.IntSyn = IntSyn' !*)

                  structure CPrint : CPRINT
                  (*! sharing CPrint.IntSyn = IntSyn' !*)
                  (*! sharing CPrint.CompSyn = CompSyn' !*)

                  structure Names : NAMES
                  (*! sharing Names.IntSyn = IntSyn' !*)
                  (*! structure CSManager : CS_MANAGER !*)
                  (*! sharing CSManager.IntSyn = IntSyn' !*)

                  structure Trace : TRACE
                  (*! sharing Trace.IntSyn = IntSyn' !*)
                      )
  : ABSMACHINE =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    structure I = IntSyn
    structure C = CompSyn

    structure T = Trace
    structure N = Names

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

    (* Wed Mar 13 10:27:00 2002 -bp  *)
    (* should probably go to intsyn.fun *)
    fun compose (G, IntSyn.Null) = G
      | compose (G, IntSyn.Decl(G', D)) = IntSyn.Decl(compose(G, G'), D)

    fun shiftSub (IntSyn.Null, s) = s
      | shiftSub (IntSyn.Decl(G, D), s) = I.dot1 (shiftSub (G, s))

    fun subgoalNum (I.Nil) = 1
      | subgoalNum (I.App (U, S)) = 1 + subgoalNum S

    (* currently unused *)
    fun goalToType (C.All (D, g), s) =
          I.Pi ((I.decSub (D,s), I.Maybe), goalToType (g, I.dot1 s))
      | goalToType (C.Impl (_, A, _, g), s) =
          I.Pi ((I.Dec (NONE, I.EClo (A, s)), I.No), goalToType (g, I.dot1 s))
      | goalToType (C.Atom(p), s) =
          I.EClo (p, s)

  (* solve' ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated to

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve' ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) = matchAtom ((p,s), dp, sc)
    | solve' ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
        val D' as I.Dec(SOME(x),_) = N.decUName (G, I.Dec(NONE, I.EClo(A,s)))
        val _ = T.signal (G, T.IntroHyp (Ha, D'))
      in
        solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                (fn M => (T.signal (G, T.DischargeHyp (Ha, D'));
                          sc (I.Lam (D', M)))))
      end
    | solve' ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
        val D' as I.Dec(SOME(x),V) = N.decUName (G, I.decSub (D, s))
        val Ha = I.targetHead V
        val _ = T.signal (G, T.IntroParm (Ha, D'))
      in
        solve' ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
                (fn M => (T.signal (G, T.DischargeParm (Ha,  D'));
                          sc (I.Lam (D', M)))))
      end

  (* rSolve' ((p,s'), (r,s), dp, (Hc, Ha), sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- r  resgoal
       G |- s' : G''
       G'' |- p : H @ S' (mod whnf)
       if G |- S : r[s]
       then sc S is evaluated
       Hc is the clause which generated this residual goal
       Ha is the target family of p and r (which must be equal)
     Effects: instantiation of EVars in p[s'], r[s], and dp
              any effect  sc S  might have
  *)
  and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), HcHa, sc) =
      (T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps'));
       case Unify.unifiable' (G, (Q, s), ps') (* effect: instantiate EVars *)
         of NONE => (T.signal (G, T.Resolved HcHa);
                     sc I.Nil;                  (* call success continuation *)
                     true)                      (* deep backtracking *)
          | SOME(msg) => (T.signal (G, T.FailUnify (HcHa, msg));
                          false))               (* shallow backtracking *)


    | rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), HcHa, sc) =
      (* Do not signal unification events for optimized clauses *)
      (* Optimized clause heads lead to unprintable substitutions *)
      ((* T.signal (G, T.Unify (HcHa, I.EClo (Q, s), I.EClo ps')); *)
       case Assign.assignable (G, ps', (Q, s))
         of SOME(cnstr) => aSolve((eqns, s), dp, HcHa, cnstr, (fn () => sc I.Nil))
          | NONE => ((* T.signal (G, T.FailUnify (HcHa, "Assignment failed")); *)
                     false))

    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), HcHa, sc) =
      let
        (* is this EVar redundant? -fp *)
        val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, HcHa,
                (fn S =>
                 (T.signal (G, T.Subgoal (HcHa, fn () => subgoalNum S));
                  solve' ((g, s), dp, (fn M => sc (I.App (M, S)))))))
      end
    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), HcHa, sc) =
      let
        val X = I.newEVar (G, I.EClo (A,s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, HcHa, (fn S => sc (I.App(X,S))))
      end
    | rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), HcHa, sc) =
      let
        val X = I.newAVar ()
      in
        rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), s)), dp, HcHa, sc)
        (* we don't increase the proof term here! *)
      end

  (* aSolve ((ag, s), dp, HcHa, sc) = T
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated

     Effects: instantiation of EVars in ag[s], dp and sc () *)


  and aSolve ((C.Trivial, s), dp as C.DProg(G, dPool), HcHa, cnstr, sc) =
        if Assign.solveCnstr cnstr then
           (T.signal (G, T.Resolved HcHa);
            sc (); true)
        else
          ((* T.signal (G, T.FailUnify (HcHa, "Dynamic residual equations failed")); *)
           false)
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), HcHa, cnstr, sc) =
      let
        val G'' = compose (G, G')
        val s' = shiftSub (G', s)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s'))
           then aSolve ((eqns, s), dp, HcHa, cnstr, sc)
        else ((* T.signal (G, T.FailUnify (HcHa, "Static residual equations failed")); *)
              false)
     end

  (* matchatom ((p, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated with return value res
       else res = False
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        val tag = T.tagGoal ()
        val _ = T.signal (G, T.SolveGoal (tag, Ha, I.EClo ps'))

        val deterministic = C.detTableCheck (cidFromHead Ha)
        exception SucceedOnce of I.Spine

        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)

        fun matchSig nil =
            (T.signal (G, T.FailGoal (tag, Ha, I.EClo ps'));
             ())        (* return on failure *)
          | matchSig (Hc::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
            in
              (* trail to undo EVar instantiations *)
              if
                CSManager.trail (fn () =>
                                 rSolve (ps', (r, I.id), dp, (Hc, Ha),
                                         (fn S => (T.signal (G, T.SucceedGoal (tag, (Hc, Ha), I.EClo ps'));
                                                   sc (I.Root(Hc, S))))))
                then (* deep backtracking *)
                  (T.signal (G, T.RetryGoal (tag, (Hc, Ha), I.EClo ps'));
                   ())
              else (* shallow backtracking *)
                ();
              matchSig sgn'
            end

        (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1. -- succeeds exactly once

           succeeds exactly once (#succeeds = 1)
        *)
        fun matchSigDet nil =
            (T.signal (G, T.FailGoal (tag, Ha, I.EClo ps'));
             ())        (* return on failure *)
          | matchSigDet (Hc::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
            in
              (* trail to undo EVar instantiations *)
              (if
                CSManager.trail (fn () =>
                                 rSolve (ps', (r, I.id), dp, (Hc, Ha),
                                         (fn S => (T.signal (G, T.SucceedGoal (tag, (Hc, Ha), I.EClo ps'));
                                                   raise SucceedOnce S))))
                then (* deep backtracking *)
                  (T.signal (G, T.RetryGoal (tag, (Hc, Ha), I.EClo ps'));
                   ())
              else (* shallow backtracking *)
                ();
              matchSigDet sgn')
              handle SucceedOnce S => (T.signal (G, T.CommitGoal (tag, (Hc, Ha), I.EClo ps'));
                                       sc (I.Root(Hc, S)))
            end

        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
        fun matchDProg (I.Null, _) =
            (* dynamic program exhausted, try signature *)
            if deterministic
              then matchSigDet (Index.lookup (cidFromHead Ha))
            else matchSig (Index.lookup (cidFromHead Ha))
          | matchDProg (I.Decl (dPool', C.Dec(r, s, Ha')), k) =
            if eqHead (Ha, Ha')
            then
              (if deterministic
                 then (* #succeeds = 1 *)
                   ((if (CSManager.trail (* trail to undo EVar instantiations *)
                        (fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,(I.BVar(k), Ha),
                                          (fn S => (T.signal (G, T.SucceedGoal (tag, (I.BVar(k), Ha), I.EClo ps'));
                                                    raise SucceedOnce S)))))
                      then (* deep backtracking *)
                        (T.signal (G, T.RetryGoal (tag, (I.BVar(k), Ha), I.EClo ps'));
                         ())
                    else (* shallow backtracking *)
                      ();
                      matchDProg (dPool', k+1))
                    handle SucceedOnce S => (T.signal (G, T.CommitGoal (tag, (I.BVar(k), Ha), I.EClo ps'));
                                             sc (I.Root(I.BVar(k), S))))

               else (* #succeeds >= 1 -- allows backtracking *)
                 (if
                    CSManager.trail (fn () =>
                                     rSolve (ps', (r, I.comp(s, I.Shift(k))),
                                             dp, (I.BVar(k), Ha),
                                             (fn S => (T.SucceedGoal (tag, (I.BVar(k), Ha), I.EClo ps');
                                                       sc (I.Root(I.BVar(k), S))))))
                    then (* deep backtracking *)
                      (T.signal (G, T.RetryGoal (tag, (I.BVar(k), Ha), I.EClo ps'));
                       ())
                  else (* shallow backtracking *)
                    ();
                    matchDProg (dPool', k+1)))
            else matchDProg (dPool', k+1)
          | matchDProg (I.Decl (dPool', C.Parameter), k) =
              matchDProg (dPool', k+1)
        fun matchConstraint (cnstrSolve, try) =
              let
                val succeeded =
                  CSManager.trail
                    (fn () =>
                       case (cnstrSolve (G, I.SClo (S, s), try))
                         of SOME(U) => (sc U; true)
                          | NONE => false)
              in
                if succeeded
                then matchConstraint (cnstrSolve, try+1)
                else ()
              end
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, cnstrSolve)) => matchConstraint (cnstrSolve, 0)
           | _ => matchDProg (dPool, 1)
      end

  in
    fun solve (gs, dp, sc) = (T.init(); solve' (gs, dp, sc))
  end (* local ... *)

end; (* functor TMachine *)
