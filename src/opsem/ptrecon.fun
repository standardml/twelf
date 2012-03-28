(* Abstract Machine execution guided by proof skeleton *)
(* Author: Brigitte Pientka *)
(* Modified: Jeff Polakow, Frank Pfenning, Larry Greenfield, Roberto Virga, Brigitte Pientka *)

(* Proof term reconstruction from proof skeleton *)

functor PtRecon ((*! structure IntSyn' : INTSYN !*)
                 (*! structure CompSyn' : COMPSYN !*)
                    (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                    structure Unify : UNIFY
                    (*! sharing Unify.IntSyn = IntSyn' !*)
                    structure Assign : ASSIGN
                    (*! sharing Assign.IntSyn = IntSyn' !*)
                    (*! structure TableParam : TABLEPARAM !*)
                    structure MemoTable : MEMOTABLE
                    (*! sharing MemoTable.TableParam = TableParam !*)
                    structure Index : INDEX
                    (*! sharing Index.IntSyn = IntSyn' !*)
                    (* CPrint currently unused *)
                    structure CPrint : CPRINT
                    (*! sharing CPrint.IntSyn = IntSyn' !*)
                    (*! sharing CPrint.CompSyn = CompSyn' !*)
                    structure Names : NAMES
                    (*! sharing Names.IntSyn = IntSyn' !*)
                    (*! structure CSManager : CS_MANAGER !*)
                    (*! sharing CSManager.IntSyn = IntSyn' !*)
                        )
  : PTRECON =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  (*! structure TableParam = TableParam !*)

  local
    structure I = IntSyn
    structure C = CompSyn
    structure MT = MemoTable
  in

    exception Error of string

    fun cidFromHead (I.Const a) = a
      | cidFromHead (I.Def a) = a

    fun eqHead (I.Const a, I.Const a') = a = a'
      | eqHead (I.Def a, I.Def a') = a = a'
      | eqHead _ = false

  fun compose'(IntSyn.Null, G) = G
    | compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D)

  fun shift (IntSyn.Null, s) = s
    | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

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

     Non-determinism within the rules is resolved by oracle
  *)

  (* solve' (o, (g, s), dp, sc) => ()
     Invariants:
       o = oracle
       dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
       G |- s : G'
       G' |- g  goal
       if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
              any effect  sc M  might have
  *)
  fun solve' (O, (C.Atom(p), s), dp as C.DProg (G, dPool), sc) =
    matchAtom (O, (p,s), dp, sc)
    | solve' (O, (C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
      let
        val D' = I.Dec(NONE, I.EClo(A,s))
      in
         if (!TableParam.strengthen)
           then
             (case MT.memberCtx ((G,I.EClo(A,s)), G) of
                SOME(D) =>
                  let
                     val X = I.newEVar(G, I.EClo(A, s))
                   in
                     (* need to reuse label for this assumption .... *)
                     solve' (O, (g, I.Dot(I.Exp(X),s)), C.DProg (G, dPool), (fn (O,M) => sc (O, I.Lam(D',M))))
                   end
                 | NONE => solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                                  (fn (O,M) => sc (O,I.Lam (D', M)))))
         else
           solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                  (fn (O,M) => sc (O, (I.Lam (D', M)))))
(*      solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
               (fn (O,M) => sc (O, (I.Lam (D', M)))))*)
      end
    | solve' (O, (C.All(D, g), s), C.DProg (G, dPool), sc) =
      let
        val D' = Names.decLUName (G, I.decSub (D, s))
        (* val D' = I.decSub (D, s) *)
      in
        solve' (O, (g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
               (fn (O, M) => sc (O, (I.Lam (D', M)))))
      end

  (* rsolve (O, (p,s'), (r,s), dp, sc) = ()
     Invariants:
       O = oracle
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
  and rSolve (O, ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =
      if Unify.unifiable (G, (Q, s), ps') (* effect: instantiate EVars *)
        then sc (O, I.Nil)                (* call success continuation *)
      else (let val _ = (print "Unification Failed -- SHOULD NEVER HAPPEN!\n";
                         print (Print.expToString (G, I.EClo(ps')) ^ " unify ");
                         print (Print.expToString (G, I.EClo(Q, s)) ^ "\n"))
            in
              ()
            end)
          (* fail *)

    | rSolve (O, ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
        (case Assign.assignable (G, ps', (Q, s)) of
          SOME(cnstr) =>
            if aSolve((eqns, s), dp, cnstr)
              then sc (O, I.Nil)
            else  print "aSolve cnstr not solvable -- SHOULD NEVER HAPPEN\n"
        | NONE => print "Clause Head not assignable -- SHOULD NEVER HAPPEN\n")

    | rSolve (O, ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (O, ps', (r, I.Dot(I.Exp(X), s)), dp,
                (fn (O, S) => solve' (O, (g, s), dp,
                                (fn (O, M) => sc (O, (I.App (M, S)))))))
      end
    | rSolve (O, ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
      let
        val X = I.newEVar (G, I.EClo (A,s))
      in
        rSolve (O, ps', (r, I.Dot(I.Exp(X), s)), dp,
                (fn (O,S) => sc (O, (I.App(X,S)))))
      end

    | rSolve (O, ps', (C.Axists(I.ADec(SOME(X), d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        val X' = I.newAVar ()
      in
        rSolve (O, ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
        (* we don't increase the proof term here! *)
      end

  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr) =
       Assign.solveCnstr cnstr
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr) =
      let
        val (G'') = compose'(G', G)
        val s' = shift (G', s)
      in
         Assign.unifiable (G'', (N, s'), (e1, s')) andalso
              aSolve ((eqns, s), dp, cnstr)
     end


  (* matchatom (O, (p, s), dp, sc) => ()
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
  and matchAtom ((Ho::O), ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        fun matchSig (nil, k) =
             raise Error (" \noracle #Pc does not exist \n")
             (* should not happen *)
          | matchSig (((Hc as (I.Const c))::sgn'), k) =
            if c = k then
              let
                val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
              in
                rSolve (O, ps', (r, I.id), dp,
                        (fn (O,S) => sc (O, (I.Root(Hc, S)))))
              end
            else
              matchSig (sgn', k)
          | matchSig (((Hc as (I.Def d))::sgn'), k) =
            if d = k then
              let
                val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
              in
                rSolve (O, ps', (r, I.id), dp,
                        (fn (O,S) => sc (O, (I.Root(Hc, S)))))
              end
            else
              matchSig (sgn', k)

        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
        fun matchDProg (I.Null, i, k) =
            (* dynamic program exhausted -- shouldn't happen *)
            raise Error ("\n selected dynamic clause number does not exist in current dynamic clause pool!\n")
          | matchDProg (I.Decl (dPool', C.Dec (r, s, Ha')), 1, k) =
            if eqHead (Ha, Ha')
              then
                rSolve (O, ps', (r, I.comp(s, I.Shift(k))), dp,
                        (fn (O,S) => sc (O, (I.Root(I.BVar(k), S)))))
            else (* shouldn't happen *)
              raise Error ("\n selected dynamic clause does not match current goal!\n")

          | matchDProg (I.Decl (dPool', dc), i ,k) =
              matchDProg (dPool', i-1, k)
      in
        (case Ho of
           C.Pc i => matchSig (Index.lookup (cidFromHead Ha), i)
         | C.Dc i => matchDProg (dPool, i, i)
         | C.Csolver U => sc (O, U))
      end


  fun solve (O, (g, s), dp as C.DProg(G, dPool), sc) =
      solve' (O, (g,s), dp, sc) handle Error msg => print msg

  end (* local ... *)

end; (* functor PtRecon *)
