(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga *)

functor AbsMachine ((*! structure IntSyn' : INTSYN !*)
                    (*! structure CompSyn' : COMPSYN !*)
                    (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                    structure Unify : UNIFY
                    (*! sharing Unify.IntSyn = IntSyn' !*)

                    structure Assign : ASSIGN
                    (*! sharing Assign.IntSyn = IntSyn' !*)

                    structure Index : INDEX
                    (*! sharing Index.IntSyn = IntSyn' !*)
                    (* CPrint currently unused *)
                    structure CPrint : CPRINT
                    (*! sharing CPrint.IntSyn = IntSyn' !*)
                    (*! sharing CPrint.CompSyn = CompSyn' !*)

                    structure Print : PRINT
                    (*! sharing Print.IntSyn = IntSyn' !*)

                    structure Names : NAMES
                    (*! sharing Names.IntSyn = IntSyn' !*)
                    (*! structure CSManager : CS_MANAGER !*)
                    (*! sharing CSManager.IntSyn = IntSyn' !*)
                        )
  : ABSMACHINE =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)

  local
    structure I = IntSyn
    structure C = CompSyn

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

  fun raiseType (I.Null, V) = V
    | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))

  (* solve ((g, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated

     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) =
      matchAtom ((p,s), dp, sc)

    | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
        val D' = I.Dec(NONE, I.EClo(A,s))
      in
        solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                (fn M => sc (I.Lam (D', M))))
      end
    | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
        val D' = Names.decLUName (G, I.decSub (D, s))
(*      val D' = I.decSub (D, s) *)
      in
        solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
                (fn M => sc (I.Lam (D', M))))
      end

  (* rSolve ((p,s'), (r,s), dp, sc) = ()
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
       if Unify.unifiable (G, (Q, s), ps') (* effect: instantiate EVars *)
         then sc I.Nil                     (* call success continuation *)
       else ()                             (* fail *)

    | rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
        (case Assign.assignable (G, ps', (Q, s))
           of SOME(cnstr) =>
                aSolve((eqns, s), dp, cnstr, (fn () => sc I.Nil))
            | NONE => ())

    | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        (* same effect as s^-1 *)
        val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
                (fn S => solve ((g, s), dp, (fn M => sc (I.App (M, S))))))
      end

    | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
        val X  = I.newEVar (G, I.EClo (A,s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, (fn S => sc (I.App(X,S))))
      end
    | rSolve (ps', (C.Axists(I.ADec(_, d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        val X' = I.newAVar ()
      in
        rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
        (* we don't increase the proof term here! *)
      end

  (* aSolve ((ag, s), dp, sc) = ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr, sc) =
      if Assign.solveCnstr cnstr then
        sc ()
      else ()
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        val G'' = compose (G, G')
        val s' = shiftSub (G', s)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s'))
        then
           aSolve ((eqns, s), dp, cnstr, sc)
        else ()
     end

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
        val deterministic = C.detTableCheck (cidFromHead Ha)
        exception SucceedOnce of I.Spine
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           #succeeds >= 1 (succeeds at least once)
        *)
        fun matchSig nil = ()   (* return unit on failure *)
          | matchSig (Hc::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
            in
              (* trail to undo EVar instantiations *)
              CSManager.trail
              (fn () =>
               rSolve (ps', (r, I.id), dp, (fn S => sc (I.Root(Hc, S)))));
              matchSig sgn'
            end

        (* matchSigDet [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.

           succeeds exactly once (#succeeds = 1)
        *)
        fun matchSigDet nil = ()        (* return unit on failure *)
          | matchSigDet (Hc::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
            in
              (* trail to undo EVar instantiations *)
              (CSManager.trail
               (fn () => (rSolve (ps', (r, I.id), dp, (fn S =>  raise SucceedOnce S))));
               matchSigDet sgn')
              handle SucceedOnce S =>  sc (I.Root(Hc, S))
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
              if deterministic
                then (* #succeeds = 1 *)
                  ((CSManager.trail (* trail to undo EVar instantiations *)
                    (fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                     (fn S => (raise SucceedOnce S))));
                    matchDProg (dPool', k+1))
                   handle SucceedOnce S => sc (I.Root(I.BVar(k), S)))

              else (* #succeeds >= 1 -- allows backtracking *)
                (CSManager.trail (* trail to undo EVar instantiations *)
                 (fn () => rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                   (fn S => sc (I.Root(I.BVar(k), S)))));
                 matchDProg (dPool', k+1))
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
   val solve = solve
  end (* local ... *)

end; (* functor AbsMachine *)
