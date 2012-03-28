(* Search (based on abstract machine ) : Version 1.3 *)
(* Author: Carsten Schuermann *)

functor Search
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure Data : DATA
   structure CompSyn' : COMPSYN
   (*! sharing CompSyn'.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Assign : ASSIGN
   (*! sharing Assign.IntSyn = IntSyn' !*)
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)
   structure Compile : COMPILE
   (*! sharing Compile.IntSyn = IntSyn' !*)
   (*! sharing Compile.CompSyn = CompSyn' !*)
   structure CPrint : CPRINT
   (*! sharing CPrint.IntSyn = IntSyn' !*)
   (*! sharing CPrint.CompSyn = CompSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure CSManager : CS_MANAGER
   (*! sharing CSManager.IntSyn = IntSyn' !*)
       )
     : SEARCH =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'
  (*! structure CompSyn = CompSyn' !*)

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

    fun compose'(IntSyn.Null, G) = G
      | compose'(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose'(G, G'), D)

    fun shift (IntSyn.Null, s) = s
      | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))


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
(*      | occursInExpW (r, (I.FgnExp (cs, ops), s)) =
          occursInExp (r, (#toInternal(ops)(), s)) *)
          (* hack - should consult cs  -rv *)

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
      | selectEVar ((X as I.EVar (r, _, _, ref nil)) :: GE) =
        let
          val Xs = selectEVar (GE)
        in
          if nonIndex (r, Xs) then Xs @ [X]
          else Xs
        end
      | selectEVar ((X as I.EVar (r, _, _, cnstrs)) :: GE) =  (* Constraint case *)
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

  fun cidFromHead (I.Const a) = a
    | cidFromHead (I.Def a) = a
    | cidFromHead (I.Skonst a) = a

  (* only used for type families of compiled clauses *)
  fun eqHead (I.Const a, I.Const a') = a = a'
    | eqHead (I.Def a, I.Def a') = a = a'
    | eqHead _ = false

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
  fun solve (max, depth, (C.Atom p, s), dp, sc) = matchAtom (max, depth, (p,s), dp, sc)
    | solve (max, depth, (C.Impl (r, A, Ha, g), s), C.DProg (G, dPool), sc) =
       let
         val D' = I.Dec (NONE, I.EClo (A, s))
       in
         solve (max, depth+1, (g, I.dot1 s),
                C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec (r, s, Ha))),
                (fn M => sc (I.Lam (D', M))))
       end
    | solve (max, depth, (C.All (D, g), s), C.DProg (G, dPool), sc) =
       let
         val D' = I.decSub (D, s)
       in
         solve (max, depth+1, (g, I.dot1 s),
                C.DProg (I.Decl (G, D'), I.Decl (dPool, C.Parameter)),
                (fn M => sc (I.Lam (D', M))))
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
  and rSolve (max, depth, ps', (C.Eq Q, s), C.DProg (G, dPool), sc) =
      if Unify.unifiable (G, ps', (Q, s))
        then sc I.Nil
      else ()
      (* replaced below by above.  -fp Mon Aug 17 10:41:09 1998
        ((Unify.unify (ps', (Q, s)); sc (I.Nil, acck)) handle Unify.Unify _ => acc) *)

    | rSolve (max, depth, ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
         (case Assign.assignable (G, ps', (Q, s))
            of SOME(cnstr) =>
               aSolve((eqns, s), dp, cnstr, (fn () => sc I.Nil))
             | NONE => ())

    | rSolve (max, depth, ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
        (* is this EVar redundant? -fp *)
        val X = I.newEVar (G, I.EClo(A, s))
      in
        rSolve (max, depth, ps', (r, I.Dot(I.Exp(X), s)), dp,
                (fn S => solve (max, depth, (g, s), dp,
                                (fn M => sc (I.App (M, S))))))

      end
    | rSolve (max, depth, ps', (C.In (r, A, g), s), dp as C.DProg (G, dPool), sc) =
      let
                                        (* G |- g goal *)
                                        (* G |- A : type *)
                                        (* G, A |- r resgoal *)
                                        (* G0, Gl  |- s : G *)
        val G0 = pruneCtx (G, depth)
        val dPool0 = pruneCtx (dPool, depth)
        val w = I.Shift (depth)         (* G0, Gl  |- w : G0 *)
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
                (fn S =>
                 if isInstantiated X then sc (I.App (X', S))
                 else  solve (max, 0, (g, s'), C.DProg (G0, dPool0),
                              (fn M =>
                               ((Unify.unify (G0, (X, I.id), (M, I.id));
                                 sc (I.App (I.EClo (M, w), S)))
                                handle Unify.Unify _ => ())))))
      end
    | rSolve (max, depth, ps', (C.Exists (I.Dec (_, A), r), s), dp as C.DProg (G, dPool), sc) =
        let
          val X = I.newEVar (G, I.EClo (A, s))
        in
          rSolve (max, depth, ps', (r, I.Dot (I.Exp (X), s)), dp,
                  (fn S => sc (I.App (X, S))))
        end
    | rSolve (max, depth, ps', (C.Axists(I.ADec(SOME(X), d), r), s), dp as C.DProg (G, dPool), sc) =
      let
        val X' = I.newAVar ()
      in
        rSolve (max, depth, ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
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

  and aSolve ((C.Trivial, s), dp, cnstr, sc) =
        (if Assign.solveCnstr cnstr then
          sc ()
        else
           ())
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        val (G'') = compose'(G', G)
        val s' = shift (G', s)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s')) then
              aSolve ((eqns, s), dp, cnstr, sc)
        else ()
     end

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
  and matchAtom (0, _, _, _, _) = ()
    | matchAtom (max, depth,
                 ps' as (I.Root (Ha, _), _),
                 dp as C.DProg (G, dPool), sc) =
      let
        fun matchSig' nil = ()
          | matchSig' (Hc ::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
              val _ = CSManager.trail
                      (fn () =>
                       rSolve (max-1, depth, ps', (r, I.id), dp,
                               (fn S => sc (I.Root (Hc, S)))))
            in
              matchSig' sgn'
            end

        fun matchBlock (nil, (n, i)) = ()
          | matchBlock ((r, s, H') :: RGs', (n, i)) =
            if eqHead (Ha, H') then
              let
                val _ = CSManager.trail (fn () =>
                            rSolve (max-1,depth, ps', (r, I.comp (s, I.Shift n)), dp,
                                    (fn S => sc (I.Root (I.Proj (I.Bidx n, i), S)))))
              in
                matchBlock (RGs', (n, i+1))
              end
            else matchBlock (RGs', (n, i+1))


        fun matchDProg (I.Null, _) = matchSig' (Index.lookup (cidFromHead Ha))
          | matchDProg (I.Decl (dPool', C.Dec (r, s, Ha')), n) =
            if eqHead (Ha, Ha') then
              let
                val _ = CSManager.trail (fn () =>
                            rSolve (max-1,depth, ps', (r, I.comp (s, I.Shift n)), dp,
                                    (fn S => sc (I.Root (I.BVar n, S)))))
              in
                matchDProg (dPool', n+1)
              end
            else matchDProg (dPool', n+1)
          | matchDProg (I.Decl (dPool', C.Parameter), n) =
              matchDProg (dPool', n+1)
          | matchDProg (I.Decl (dPool', C.BDec RGs), n) =
              (matchBlock (RGs, (n, 1)); matchDProg (dPool', n+1))
          | matchDProg (I.Decl (dPool', C.PDec), n) =
              matchDProg (dPool', n+1)
      in
        matchDProg (dPool, 1)
      end


    (* searchEx' max (GE, sc) = acc'

       Invariant:
       If   GE is a list of EVars to be instantiated
       and  max is the maximal number of constructors
       then if an instantiation of EVars in GE is found Success is raised
            otherwise searchEx' terminates with []
    *)
    (* contexts of EVars are recompiled for each search depth *)
    and searchEx' max (nil, sc) = sc max
        (* Possible optimization:
           Check if there are still variables left over
        *)
      | searchEx' max ((X as I.EVar (r, G, V, _)) :: GE, sc) =
          solve (max, 0, (Compile.compileGoal (G, V), I.id),
                 Compile.compileCtx false G,
                 (fn U' => (Unify.unify (G, (X, I.id), (U', I.id));
                                         searchEx' max (GE, sc)) handle Unify.Unify _ => ()))

    (* deepen (f, P) = R'

       Invariant:
       If   f function expecting parameters P
         checking the variable MTPGlobal.maxLevel
       then R' is the result of applying f to P and
         traversing all possible numbers up to MTPGlobal.maxLevel
    *)
    fun deepen depth f P =
        let
          fun deepen' level =
            if level > depth then ()
            else (if !Global.chatter > 5 then print "#" else ();
                    (f level P;
                     deepen' (level+1)))
        in
          deepen' 1
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

    (* search (GE, sc) = ()

       Invariant:
       GE is a list of uninstantiated EVars
       and sc is a success continuation : int -> unit

       Side effect:
       success continuation will raise exception
    *)
    (* Shared contexts of EVars in GE may recompiled many times *)
    fun search (maxFill, GE, sc) = searchEx (1, maxFill) (GE, sc)

  in
    val searchEx = search
  end (* local ... *)

end; (* functor Search *)

