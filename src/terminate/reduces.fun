(* Reduction and Termination checker *)
(* Author: Brigitte Pientka *)
(* for termination checking see [Rohwedder,Pfenning ESOP'96]
   for a revised version incorporating reducation checking see
   tech report CMU-CS-01-115
 *)

functor Reduces   (structure Global : GLOBAL
                   (*! structure IntSyn' : INTSYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = IntSyn' !*)
                   structure Index : INDEX
                   (*! sharing Index.IntSyn = IntSyn' !*)
                   structure Subordinate : SUBORDINATE
                   (*! sharing Subordinate.IntSyn = IntSyn' !*)
                   structure Formatter : FORMATTER
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn' !*)
                     sharing Print.Formatter = Formatter
                   structure Order : ORDER
                   (*! sharing Order.IntSyn = IntSyn' !*)
                   (*! structure Paths  : PATHS !*)
                   structure Checking : CHECKING
                      sharing Checking.Order = Order
                      (*! sharing Checking.IntSyn = IntSyn' !*)
                      (*! sharing Checking.Paths = Paths !*)
                   structure Origins : ORIGINS
                   (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Origins.IntSyn = IntSyn' !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn' !*)
                       )
  :  REDUCES =
struct
  (*! structure IntSyn = IntSyn' !*)

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

    fun concat (G', I.Null) = G'
      | concat (G', I.Decl(G, D)) = I.Decl(concat(G', G), D)
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
                  fmtPredicate (I.Decl(G, D), P)]

    fun rlistToString' (G, nil) = ""
      | rlistToString' (G, [P]) =
        F.makestring_fmt(fmtPredicate (G, P) )
      | rlistToString' (G, (P::Rl)) =
        F.makestring_fmt(fmtPredicate (G, P)) ^ " ," ^ rlistToString' (G, Rl)

    fun rlistToString (G, Rl) = rlistToString' (Names.ctxName G, Rl)

    fun orderToString (G, P) = F.makestring_fmt(fmtPredicate (Names.ctxName G, P))


   (*--------------------------------------------------------------------*)
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

    (* abstractRO (G, D, RO) = Pi D. RO
       Invariant:

       If  G, D |- RO
       then  G |- Pi D . RO

    *)

    fun abstractRO (G, D, O) = C.Pi(D, O)

    (* getROrder (G, Q, (V, s)) = O
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       then O is the reduction order associated to V[s]
       and  G |- O

     *)
    fun getROrder (G, Q, Vs, occ) = getROrderW (G, Q, Whnf.whnf Vs, occ)
    and getROrderW (G, Q, Vs as (I.Root (I.Const a, S), s), occ) =
         let
           val O = selectROrder (a, (S, s))
           val _ = case O
                    of NONE => ()
                     | SOME(O) => if (!Global.chatter) > 5
                                       then print ("Reduction predicate for " ^
                                                   N.qidToString (N.constQid a) ^
                                                   " added : " ^
                                                   orderToString (G, O) ^ "\n")
                                      else ()
         in
           O
         end
      | getROrderW (G, Q, (I.Pi ((D, I.Maybe), V), s), occ) =
          let
            val O = getROrder (I.Decl (G, N.decLUName (G, I.decSub (D, s))),
                                I.Decl (Q, C.All), (V, I.dot1 s), P.body occ)
          in
            case O
              of NONE => NONE
               | SOME(O') => SOME(abstractRO(G, I.decSub(D, s), O'))
          end
      | getROrderW (G, Q, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
          let
            val O = getROrder (G, Q, (V2, I.comp(I.invShift, s)), P.body occ)
          in
            case O
              of NONE => NONE
               | SOME(O') => SOME(O')
          end
      | getROrderW (G, Q, Vs as (I.Root (I.Def a, S), s), occ) =
          raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
                        ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")

    (*--------------------------------------------------------------------*)

    (* Termination Checker *)
    (* checkGoal (G0, Q0, Rl, (V, s), (V', s'), occ) = ()

       Invariant:
       If   G0 : Q0
       and  G0 |- s : G1     and   G1 |- V : L     (V, s) in whnf
       and  V[s], V'[s'] does not contain Skolem constants
       and  G0 |- s' : G2    and   G2 |- V' : L'   (V', s') in whnf
       and  V' = a' @ S'
       and  G |- L = L'
       and  V[s] < V'[s']  (< termination ordering)
         then ()
       else Error is raised.
    *)

    fun checkGoal (G0, Q0, Rl, Vs, Vs', occ) =
          checkGoalW (G0, Q0, Rl, Whnf.whnf Vs, Vs', occ)
    and checkGoalW (G0, Q0, Rl, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), Vs', occ) =
        (checkClause ((G0, Q0, Rl), I.Null, I.Null, (V1, s), P.label occ);
         checkGoal (G0, Q0, Rl, (V2, I.comp(I.invShift, s)), Vs', P.body occ))
      | checkGoalW (G0, Q0, Rl, (I.Pi ((D, I.Maybe), V), s), (V', s'), occ) =
        checkGoal (I.Decl (G0, N.decLUName (G0, I.decSub (D, s))),
                     I.Decl (Q0, C.All),
                     C.shiftRCtx Rl (fn s => I.comp(s, I.shift)),
                     (V, I.dot1 s), (V', I.comp(s', I.shift)), P.body occ)
      | checkGoalW (G0, Q0, Rl, Vs as (I.Root (I.Const a, S), s),
                    Vs' as (I.Root (I.Const a', S'), s'), occ) =
        let
          fun lookup (R.Empty, f) = R.Empty
            | lookup (a's as R.LE (a, a's'), f) =
                if (f a) then a's else lookup (a's', f)
            | lookup (a's as R.LT (a, a's'), f) =
                if (f a) then a's else lookup (a's', f)
          val P = selectOcc (a, (S, s), occ)    (* only if a terminates? *)
          val P' = select (a', (S', s')) (* always succeeds? -fp *)
          val a's = Order.mutLookup a   (* always succeeds? -fp *)
        in
          (case lookup (a's, fn x' => x' = a')
             of R.Empty => ()
              | R.LE _ => (if (!Global.chatter) > 4
                             then (print ("Verifying termination order:\n");
                                   print (rlistToString (G0, Rl));
                                   print( " ---> " ^ orderToString (G0, C.Leq(P, P')) ^ "\n"))
                           else ();
                           if C.deduce (G0, Q0, Rl, C.Leq(P, P'))
                             then ()
                           else raise Error' (occ, "Termination violation:\n" ^
                                              rlistToString (G0, Rl) ^ " ---> " ^
                                              orderToString (G0, C.Leq(P, P'))))
             | R.LT _ =>  (if (!Global.chatter) > 4
                            then  (print "Verifying termination order:\n";
                                   print (rlistToString (G0, Rl) ^ " ---> ");
                                   print(orderToString (G0, C.Less(P, P')) ^ "\n"))
                           else ();
                           if C.deduce (G0, Q0, Rl, C.Less(P, P'))
                             then ()
                           else raise Error' (occ, "Termination violation:\n" ^
                                               rlistToString (G0, Rl) ^ " ---> " ^
                                               orderToString (G0, C.Less(P, P')))))
        end
      | checkGoalW (G0, Q0, Rl, Vs as (I.Root (I.Def a, S), s), Vs', occ) =
        raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
                      ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")

      | checkGoalW (G0, Q0, Rl, Vs, Vs' as (I.Root (I.Def a', S'), s'), occ) =
        raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
                        ^ "Illegal use of " ^ N.qidToString (N.constQid a') ^ ".")

    (* checkSubgoals (G0, Q0, Rl, Vs, n, (G, Q), Vs, occ)

      if    G0 |- Q0
       and  G0 |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0 |- Rl
       and  G0 |- V[s]
       and  G0 = G0', G' where G' <= G
       and  n = |G'| - |G|
       and  G0 |- G[^n]
       and  G |- Q
     and
       V[s] satisfies the associated termination order

     *)

    and checkSubgoals (G0, Q0, Rl, Vs, n, (I.Decl(G, D as I.Dec(_,V')), I.Decl(Q, C.And(occ)))) =
          let
            val _ = checkGoal (G0, Q0, Rl, (V', I.Shift (n+1)), Vs, occ)
            val RO = getROrder (G0, Q0, (V', I.Shift (n+1)), occ)
            val Rl' = case RO
                        of NONE => Rl
                          | SOME(O) => O :: Rl
          in
            checkSubgoals (G0, Q0, Rl', Vs, n+1, (G, Q))
          end
      | checkSubgoals (G0, Q0, Rl, Vs, n, (I.Decl(G, D), I.Decl(Q, C.Exist))) =
          checkSubgoals (G0, Q0, Rl, Vs, n+1, (G, Q))

      | checkSubgoals (G0, Q0, Rl, Vs, n, (I.Decl(G, D), I.Decl(Q, C.All))) =
          checkSubgoals (G0, Q0, Rl, Vs, n+1, (G, Q))

      | checkSubgoals (G0, Q0, Rl, Vs, n, (I.Null, I.Null)) = ()


    (* checkClause (GQR as (G0, Q0, Rl), G, Q, Vs, occ)

      if   G0, G |- Q0, Q
       and  G0, G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any skolem constants
       and  Rl is a list of reduction propositions
       and  G0, G |- Rl
       and  G0, G |- V[s]
     and
       V[s] satisfies the associated termination order
     *)
    and checkClause (GQR, G, Q, Vs, occ) =
         checkClauseW (GQR, G, Q, Whnf.whnf Vs, occ)

    and checkClauseW (GQR, G, Q, (I.Pi ((D, I.Maybe), V), s), occ) =
           checkClause (GQR, I.Decl(G, N.decEName (G, I.decSub (D, s))),
                        I.Decl (Q, C.Exist), (V, I.dot1 s), P.body occ)

      | checkClauseW (GQR, G, Q, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
           checkClause (GQR, I.Decl (G, I.decSub (D, s)), I.Decl (Q, C.And (P.label occ)),
                        (V2, I.dot1 s), P.body occ)

      | checkClauseW (GQR as (G0, Q0, Rl), G, Q, Vs as (I.Root (I.Const a, S), s), occ) =
          let
            val n = I.ctxLength G
            val Rl' = C.shiftRCtx Rl (fn s => I.comp(s, I.Shift n))
          in
            checkSubgoals (concat(G0, G), concat(Q0, Q), Rl', Vs, 0, (G, Q))
          end

      | checkClauseW (GQR, G, Q, (I.Root (I.Def a, S), s), occ) =
        raise Error' (occ, "Termination checking for defined type families not yet available:\n"
                      ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


    fun checkClause' (Vs, occ) =
      checkClause ((I.Null, I.Null, nil), I.Null, I.Null, Vs, occ)

    (*-------------------------------------------------------------------*)
    (* Reduction Checker *)

    (* checkRGoal (G, Q, Rl, (V1, s1), occ) = Rl''

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context of reduction predicates
       and  G |- Rl
       and Rl implies that V1[s1] satisfies its associated reduction order

     *)

     fun checkRGoal (G, Q, Rl, Vs, occ) =
           checkRGoalW (G, Q, Rl, Whnf.whnf Vs, occ)

     and checkRGoalW (G, Q, Rl, Vs as (I.Root (I.Const a, S), s), occ) = () (* trivial *)

       | checkRGoalW (G, Q, Rl, (I.Pi ((D, I.Maybe), V), s), occ) =
           checkRGoal (I.Decl (G, N.decLUName (G, I.decSub (D, s))),
                      I.Decl (Q, C.All),
                      C.shiftRCtx Rl (fn s => I.comp(s, I.shift)),
                      (V, I.dot1 s), P.body occ)

       | checkRGoalW (G, Q, Rl, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
           (checkRClause (G, Q, Rl, (V1, s), P.label occ);
            checkRGoal (G, Q, Rl, (V2, I.comp(I.invShift, s)), P.body occ))


       | checkRGoalW (G, Q, Rl, (I.Root (I.Def a, S), s), occ) =
           raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
                         ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


    (* checkRImp (G, Q, Rl, (V1, s1), (V2, s2), occ) = ()

       Invariant
       If   G : Q
       and  G |- s1 : G1   and   G1 |- V1 : type
       and  V1[s1], V2[s2] does not contain Skolem constants
       and  G |- s2 : G2   and   G2 |- V2 : type
       and occ locates V1 in declaration
       and Rl is a context for derived reduction order assumptions
       and G |- Rl

       then Rl implies that  V2[s2] satisfies its associated reduction order
            with respect to V1[s1]
    *)

    and checkRImp (G, Q, Rl, Vs, Vs', occ) =
         checkRImpW (G, Q, Rl, Whnf.whnf Vs, Vs', occ)

    and checkRImpW (G, Q, Rl, (I.Pi ((D', I.Maybe), V'), s'), (V, s), occ) =
          checkRImp (I.Decl (G, N.decEName (G, I.decSub (D', s'))),
                     I.Decl (Q, C.Exist),
                     C.shiftRCtx Rl (fn s => I.comp(s, I.shift)),
                     (V', I.dot1 s'), (V, I.comp (s, I.shift)), occ)
      | checkRImpW (G, Q, Rl, (I.Pi ((D' as I.Dec (_, V1), I.No), V2), s'), (V, s), occ) =
          let
            val Rl' = case getROrder (G, Q, (V1, s'), occ)
                         of NONE => Rl
                       | SOME(O) => O :: Rl
          in
            checkRImp (G, Q, Rl',
                    (V2, I.comp(I.invShift, s')), (V, s), occ)
          end

      | checkRImpW (G, Q, Rl, Vs' as (I.Root (I.Const a, S), s),  Vs, occ) =
          checkRGoal (G, Q, Rl, Vs, occ)
      | checkRImpW (G, Q, Rl, Vs' as (I.Root (I.Def a, S), s), Vs, occ) =
          raise Error' (occ, "Reduction checking for defined type families not yet available:\n"
                        ^ "Illegal use of " ^ N.qidToString (N.constQid a) ^ ".")


    (* checkRClause (G, Q, Rl, (V, s)) = ()

       Invariant:
       If G: Q
       and  G |- s : G1    and   G1 |- V : L
       and  V[s] does not contain any Skolem constants
       and  Rl is a context of reduction predicates
       and  G |- Rl
       then Rl implies that V[s] satifies the reduction order
    *)

    and checkRClause (G, Q, Rl, Vs, occ) = checkRClauseW (G, Q, Rl, Whnf.whnf Vs, occ)

    and checkRClauseW (G, Q, Rl, (I.Pi ((D, I.Maybe), V), s), occ) =
          checkRClause (I.Decl (G, N.decEName (G, I.decSub (D, s))),
                        I.Decl (Q, C.Exist),
                        C.shiftRCtx Rl (fn s => I.comp(s, I.shift)),
                        (V, I.dot1 s), P.body occ)

      | checkRClauseW (G, Q, Rl, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), occ) =
         let
           val G' = I.Decl (G, I.decSub (D, s))  (* N.decEName (G, I.decSub (D, s)) *)
           val Q' = I.Decl (Q, C.Exist) (* will not be used *)
           val Rl' = C.shiftRCtx Rl (fn s => I.comp(s, I.shift))
           val Rl'' = case getROrder (G', Q', (V1, I.comp (s, I.shift)), occ)
                        of NONE => Rl'
                         | SOME(O) => O :: Rl'
         in
          checkRClause (G', Q', Rl'', (V2, I.dot1 s), P.body occ);
          checkRImp (G', Q', Rl'', (V2, I.dot1 s), (V1, I.comp(s, I.shift)), P.label occ)
        end

      | checkRClauseW (G, Q, Rl, Vs as (I.Root (I.Const a, S), s), occ) =
        let
          val RO = case selectROrder (a, (S, s))
                     of NONE => raise Error' (occ, "No reduction order assigned for " ^
                                              N.qidToString (N.constQid a) ^ ".")
                      | SOME(O) => O
          val _ = if !Global.chatter > 4
                    then print ("Verifying reduction property:\n" ^
                                rlistToString (G, Rl) ^ " ---> " ^
                                orderToString (G, RO) ^ " \n")
                  else ()
        in
          if C.deduce(G, Q, Rl, RO)
            then ()
          else raise Error' (occ, "Reduction violation:\n" ^
                             rlistToString (G, Rl) ^ " ---> " ^  (* rename ctx ??? *)
                             orderToString (G, RO))
        end
      | checkRClauseW (G, Q, Rl, VS as (I.Root (I.Def a, S), s), occ) =
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
          fun checkFam' [] =
              (if !Global.chatter > 3
                 then print "\n"
               else () ; ())
            | checkFam' (I.Const(b)::bs) =
                (if (!Global.chatter) > 3 then
                   print (N.qidToString (N.constQid b) ^ " ")
                 else ();
                 (* reuse variable names when tracing *)
                 if (!Global.chatter) > 4
                   then (N.varReset IntSyn.Null; print "\n")
                 else ();
                 (( checkRClause (I.Null, I.Null, nil, (I.constType (b), I.id), P.top))
                    handle Error' (occ, msg) => error (b, occ, msg)
                         | R.Error (msg) => raise Error (msg));
                   checkFam' bs)
            | checkFam' (I.Def(d)::bs) =
                (if (!Global.chatter) > 3 then
                   print (N.qidToString (N.constQid d) ^ " ")
                 else ();
                 (* reuse variable names when tracing *)
                 if (!Global.chatter) > 4
                   then (N.varReset IntSyn.Null; print "\n")
                 else ();
                 (( checkRClause (I.Null, I.Null, nil, (I.constType (d), I.id), P.top))
                    handle Error' (occ, msg) => error (d, occ, msg)
                         | R.Error (msg) => raise Error (msg));
                   checkFam' bs)
          val _ = if (!Global.chatter) > 3
                    then print ("Reduction checking family " ^ N.qidToString (N.constQid a)
                                ^ ":\n")
                  else ()
        in
          checkFam' (Index.lookup a)
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
          fun checkFam' [] =
              (if !Global.chatter > 3
                 then print "\n"
               else () ; ())
            | checkFam' (I.Const b::bs) =
                (if (!Global.chatter) > 3 then
                   print (N.qidToString (N.constQid b) ^ " ")
                 else ();
                 (* reuse variable names when tracing *)
                 if (!Global.chatter) > 4
                   then (N.varReset IntSyn.Null; print "\n")
                 else ();
                (checkClause' ((I.constType (b), I.id), P.top)
                 handle Error' (occ, msg) => error (b, occ, msg)
                      | Order.Error (msg) => raise Error (msg));
                 checkFam' bs)
            | checkFam' (I.Def(d)::bs) =
                (if (!Global.chatter) > 3 then
                   print (N.qidToString (N.constQid d) ^ " ")
                 else ();
                 (* reuse variable names when tracing *)
                 if (!Global.chatter) > 4
                   then (N.varReset IntSyn.Null; print "\n")
                 else ();
                (checkClause' ((I.constType (d), I.id), P.top)
                 handle Error' (occ, msg) => error (d, occ, msg)
                      | Order.Error (msg) => raise Error (msg));
                 checkFam' bs)
          val _ = if (!Global.chatter) > 3
                    then print ("Termination checking family " ^ N.qidToString (N.constQid a)
                                ^ "\n")
                  else ()
        in
          checkFam' (Index.lookup a)
        end

    fun reset () = (R.reset(); R.resetROrder())

  in
    val reset = reset
    val checkFamReduction = checkFamReduction
    val checkFam = checkFam
  end (* local *)
end; (* functor Reduces  *)
