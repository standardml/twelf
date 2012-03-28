(* Reasoning about structural orders *)
(* Author: Brigitte Pientka *)
(* for reasoning about orders see [Pientka IJCAR'01] *)

functor Checking  (structure Global : GLOBAL
                   (*! structure IntSyn' : INTSYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   structure Conv : CONV
                   (*! sharing Conv.IntSyn = IntSyn' !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn' !*)
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
                   structure Origins : ORIGINS
                   (*! sharing Origins.Paths = Paths !*)
                     (*! sharing Origins.IntSyn = IntSyn' !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn' !*)
                       )
  :  CHECKING =
struct
  (*! structure IntSyn = IntSyn' !*)
  structure Order = Order
  (*! structure Paths = Paths !*)

    datatype Quantifier =        (* Quantifier to mark parameters *)
      All                        (* Q ::= All                     *)
    | Exist                      (*     | Exist                   *)
    | And of Paths.occ           (*     | And                     *)


    (* If Q marks all parameters in a context G we write   G : Q               *)

    datatype 'a Predicate =
      Less of 'a * 'a
    | Leq of 'a * 'a
    | Eq of 'a * 'a
    | Pi of IntSyn.Dec * 'a Predicate

   (* Abbreviation *)
    type order = (IntSyn.eclo * IntSyn.eclo) Order.Order

    (* reduction order assumptions (unordered) *)
    type rctx = order Predicate list

    (* mixed prefix order contex *)
    type qctx = Quantifier IntSyn.Ctx

  local
    structure I = IntSyn
    structure P = Paths
    structure N = Names
    structure F = Formatter
    structure R = Order


 (* Reasoning about order relations *)
 (*
    Typing context        G
    mixed prefix context  Q  := . | All | Existental

    Orders                0  := U[s1] : V[s2] | Lex O1 ... On | Simul O1 ... On
    Order Relation        P  := O < O' | O <= O' | O = O'

    Atomic Order Relation P' := U[s1] : V[s2] <  U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] <= U'[s1'] : V'[s2'] |
                                U[s1] : V[s2] =  U'[s1'] : V'[s2']

    Order Relation Ctx    D  := . | R , D
    Atomic Order Rel. Ctx D' := . | R',  D'

    Invariant:

    sometimes we write G |- P as an abbreviation

    if P = (O < O')    then G |- O and G |- O'
    if P = (O <= O')    then G |- O and G |- O'
    if P = (O = O')    then G |- O and G |- O'

    if O = Lex O1 .. On  then G |- O1 and ....G |- On
    if O = Simul O1 .. On  then G |- O1 and ....G |- On

    if O = U[s1] : V[s2]
      then     G : Q
           and G |- s1 : G1, G1 |- U : V1
           and G |- s2 : G2   G2 |- V : L
           and G |- U[s1] : V[s2]

  *)

   (*--------------------------------------------------------------------*)
   (* Printing atomic orders *)

    fun atomicPredToString (G, Less((Us, _), (Us', _))) =
          Print.expToString(G, I.EClo(Us)) ^ " < " ^
          Print.expToString(G, I.EClo(Us'))
      | atomicPredToString (G, Leq((Us, _), (Us', _))) =
          Print.expToString(G, I.EClo(Us)) ^ " <= " ^
          Print.expToString(G, I.EClo(Us'))
      | atomicPredToString (G, Eq((Us, _), (Us', _))) =
          Print.expToString(G, I.EClo(Us)) ^ " = " ^
          Print.expToString(G, I.EClo(Us'))

    fun atomicRCtxToString (G, nil) = " "
      | atomicRCtxToString (G, O::nil) = atomicPredToString (G, O)
      | atomicRCtxToString (G, O::D') =
          atomicRCtxToString (G, D') ^ ", " ^ atomicPredToString (G, O)

   (*--------------------------------------------------------------------*)
   (* shifting substitutions *)

   (* shiftO O f = O'

      if O is an order
         then we shift the substitutions which are associated
         with its terms by applying f to it
    *)

    fun shiftO (R.Arg ((U, us), (V, vs))) f =
            R.Arg ((U, (f us)), (V, (f vs)))
      | shiftO (R.Lex L) f = R.Lex (map (fn O => shiftO O f) L)
      | shiftO (R.Simul L) f = R.Simul (map (fn O => shiftO O f) L)

    fun shiftP (Less(O1, O2)) f = Less(shiftO O1 f, shiftO O2 f)
      | shiftP (Leq(O1, O2)) f = Leq(shiftO O1 f, shiftO O2 f)
      | shiftP (Eq(O1, O2)) f = Eq(shiftO O1 f, shiftO O2 f)
      | shiftP (Pi(D as I.Dec(X,V), P)) f = Pi(D, shiftP P f)

    fun shiftRCtx Rl f = map (fn p => shiftP p f) Rl

    fun shiftArg (Less (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Less (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Leq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Leq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))
      | shiftArg (Eq (((U1, s1), (V1, s1')), ((U2, s2), (V2, s2')))) f =
          Eq (((U1, (f s1)), (V1, (f s1'))), (((U2, (f s2)), (V2, (f s2')))))

    fun shiftACtx Rl f = map (fn p => shiftArg p f) Rl

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
        F.HOVbox0 1 0 1 [fmtOrder (G, O), F.Break, F.String comp, F.Break, fmtOrder (G, O')]

    fun fmtPredicate' (G, Less(O, O')) = fmtComparison (G, O, "<", O')
      | fmtPredicate' (G, Leq(O, O'))  = fmtComparison (G, O, "<=", O')
      | fmtPredicate' (G, Eq(O, O'))  = fmtComparison (G, O, "=", O')
      | fmtPredicate' (G, Pi(D, P))  =  (* F.String "Pi predicate"  *)
          F.Hbox [F.String "Pi ", fmtPredicate' (I.Decl (G, D), P)]

    fun fmtPredicate (G, P) = fmtPredicate' (Names.ctxName G, P)

    fun fmtRGCtx' (G, nil) = ""
      | fmtRGCtx' (G, [P]) =
        F.makestring_fmt(fmtPredicate' (G, P) )
      | fmtRGCtx' (G, (P :: Rl)) =
        F.makestring_fmt(fmtPredicate' (G, P)) ^ " ," ^ fmtRGCtx' (G, Rl)

    fun fmtRGCtx (G, Rl) = fmtRGCtx' (Names.ctxName G, Rl)


    (*--------------------------------------------------------------------*)

    (* init () = true

       Invariant:
       The inital constraint continuation
    *)
    fun init () = true

    fun eqCid(c, c') = (c = c')

    fun conv ((Us, Vs), (Us', Vs')) =
        Conv.conv (Vs, Vs') andalso
        Conv.conv (Us, Us')


    fun isUniversal (All) = true
      | isUniversal (Exist) = false
      | isUniversal (Exist') = false

    fun isExistential (All) = false
      | isExistential (Exist) = true
      | isExistential (Exist') = true

    (* isParameter (Q, X) = B

       Invariant:
       If   G |- X : V
       and  G : Q
       then B holds iff X is unrestricted (uninstantiated and free
       of constraints, or lowered only) or instantiated to a universal parameter
    *)
    fun isParameter (Q, X) = isParameterW (Q, Whnf.whnf (X, I.id))

    and isParameterW (Q, Us) =
        isUniversal (I.ctxLookup (Q, Whnf.etaContract (I.EClo Us)))
        handle Whnf.Eta => isFreeEVar (Us)

   (* isFreeEVar (Us) = true
       iff Us represents a possibly lowered uninstantiated EVar.

       Invariant: it participated only in matching, not full unification
    *)
    and isFreeEVar (I.EVar (_, _, _,ref []), _) = true   (* constraints must be empty *)
      | isFreeEVar (I.Lam (D, U), s) = isFreeEVar (Whnf.whnf (U, I.dot1 s))
      | isFreeEVar _ = false


    (* isAtomic (G, X) = true
       Invariant:
       If G |- X : V
       and G : Q
       then B holds iff X is an atomic term which is not a parameter
     *)
    fun isAtomic (GQ, Us) = isAtomicW (GQ, Whnf.whnf Us)

    and isAtomicW (GQ, (X as I.Root (I.Const c, S), s)) =
          isAtomicS (GQ, (S, s))
      | isAtomicW (GQ, (X as I.Root (I.Def c, S), s)) =
          isAtomicS (GQ, (S, s))
      | isAtomicW (GQ as (G, Q), (X as I.Root (I.BVar n, S), s)) =
           isExistential(I.ctxLookup (Q, n)) orelse isAtomicS (GQ, (S, s)) (* should disallow orelse ? *)
(*      | isAtomicW (GQ, (X as (I.EClo _))) = true   (* existential var *) *)
      | isAtomicW (GQ, _) = false

    and isAtomicS (GQ, (I.Nil, _)) = true
      | isAtomicS (GQ, (I.SClo (S, s'), s'')) =
          isAtomicS (GQ, (S, I.comp(s', s'')))
      | isAtomicS (GQ, (I.App (U', S'), s1')) = false


   (*-----------------------------------------------------------*)

    (* eq (G, ((U, s1), (V, s2)), ((U', s1'), (V', s2')), sc) = B

       Invariant:
       B holds  iff
            G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  U[s1] is unifiable with to U'[s']
       and  all restrictions in sc are satisfied
       and V[s2] is atomic
       and only U'[s'] contains EVars
    *)
    fun eq (G, (Us, Vs), (Us', Vs')) =
      Unify.unifiable (G, Vs, Vs')
      andalso Unify.unifiable (G, Us, Us')

    (* lookupEq (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
     or
     if there exists Eq(UsVs1, UsVs1') in D
        s.t. UsVs1' unifies with UsVs and
             UsVs1 unifies with UsVs' and
             all restrictions in sc are satisfied
             (symmetry)


    *)
    fun lookupEq (GQ, nil, UsVs, UsVs', sc) = false
      | lookupEq (GQ, (Less(_, _) :: D), UsVs, UsVs', sc) =
          lookupEq (GQ, D, UsVs, UsVs', sc)
      | lookupEq (GQ as (G,Q), (Eq(UsVs1, UsVs1') :: D), UsVs, UsVs', sc) =
          CSManager.trail (fn () =>
                           eq (G, UsVs1, UsVs) andalso eq (G, UsVs1', UsVs') andalso sc ())
          orelse
          CSManager.trail (fn () =>
                           eq (G, UsVs1, UsVs') andalso eq (G, UsVs1', UsVs) andalso sc ())
          orelse
          lookupEq (GQ, D, UsVs, UsVs', sc)


    (* lookupLt (GQ, D, UsVs, UsVs', sc) = B

     B holds iff

     and  D is an atomic order relation ctx
     and  UsVs and UsVs' are atomic and may contain EVars

          G : Q
     and  G |- s1 : G1   G1 |- U : V1
     and  G |- s2 : G2   G2 |- V : L
     and  G |- U[s1] : V [s2]
     and  G |- s' : G3  G3 |- U' : V'

     if there exists Less(UsVs1, UsVs1') in D
        s.t. UsVs1 unifies with UsVs and
             UsVs1' unifies with UsVs' and
             all restrictions in sc are satisfied
    *)

    fun lookupLt (GQ, nil, UsVs, UsVs', sc) = false
      | lookupLt (GQ, (Eq(_, _) :: D), UsVs, UsVs', sc) =
          lookupLt (GQ, D, UsVs, UsVs', sc)
      | lookupLt (GQ as (G,Q), (Less(UsVs1, UsVs1') :: D), UsVs, UsVs', sc) =
          CSManager.trail (fn () =>
                           eq (G, UsVs1, UsVs) andalso eq (G, UsVs1', UsVs') andalso sc ())
          orelse
          lookupLt (GQ, D, UsVs, UsVs', sc)

    (*  eqAtomic (GQ, D, D', UsVs, UsVs', sc) = B

        B iff
            UsVs unifies with UsVs'                (identity)
        or  D, UsVs = UsVs', D' ---> UsVs = UsVs'  (ctx lookup)
        or  D, UsVs' = UsVs, D' ---> UsVs = UsVs'  (ctx lookup + symmetry)
        or  D, D' ---> UsVs = UsVs' by transitivity

     *)
    fun eqAtomic (GQ as (G, Q), nil, D', UsVs, UsVs', sc) =
         CSManager.trail (fn () => eq (G, UsVs, UsVs') andalso sc ())
         orelse
         lookupEq (GQ, D', UsVs, UsVs', sc)
      | eqAtomic (GQ as (G, Q), D, D', UsVs, UsVs', sc) =
         CSManager.trail (fn () => eq (G, UsVs, UsVs') andalso sc ())
         orelse
         lookupEq (GQ, D, UsVs, UsVs', sc)
         orelse
         lookupEq (GQ, D', UsVs, UsVs', sc)
         orelse
         transEq (GQ, D, D', UsVs, UsVs', sc)


  (* transEq (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)
   and transEq (GQ as (G,Q), nil, D, UsVs, UsVs', sc) = false
     | transEq (GQ as (G,Q), (Eq(UsVs1, UsVs1') :: D), D', UsVs, UsVs', sc) =
         CSManager.trail (fn () =>
                          eq (G, UsVs1', UsVs') andalso sc ()
                          andalso eqAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic))
         orelse
         CSManager.trail (fn () =>
                          eq (G, UsVs1, UsVs') andalso sc ()
                          andalso eqAtomicR (GQ, (D @ D'), UsVs, UsVs1', sc, atomic))
         orelse
         transEq (GQ, D, (Eq(UsVs1, UsVs1') :: D'), UsVs, UsVs', sc)
     | transEq (GQ as (G,Q), (Less(UsVs1, UsVs1') :: D), D', UsVs, UsVs', sc) =
         transEq (GQ, D, D', UsVs, UsVs', sc)

  (* ltAtomic (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs <UsVs' ; D' ---> UsVs < UsVs'   (identity)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)


    and ltAtomic (GQ as (G, Q), nil, D', UsVs, UsVs', sc) =
         lookupLt (GQ, D', UsVs, UsVs', sc)

      | ltAtomic (GQ as (G, Q), D, D', UsVs, UsVs', sc) =
         lookupLt (GQ, D, UsVs, UsVs', sc)
         orelse
         lookupLt (GQ, D', UsVs, UsVs', sc)
         orelse
         transLt (GQ, D, D', UsVs, UsVs', sc)


  (* transLt (GQ, D, D', UsVs, UsVs', sc) = B

     B iff
        if D, UsVs' = UsVs1 ; D' ---> UsVs = UsVs'
          then  D, D' ---> UsVs = UsVs1            (transEq1)

        or

        if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'  (transEq2)
          then  D, D' ---> UsVs = UsVs1

       or

       if D, UsVs1 = UsVs'; D' ---> UsVs = UsVs'
         then D; UsVs1 = UsVs' D' ---> UsVs = UsVs'
   *)

   and transLt (GQ as (G,Q), nil, D, UsVs, UsVs', sc) = false
     | transLt (GQ as (G,Q), (Eq(UsVs1, UsVs1') :: D), D', UsVs, UsVs', sc) =
         CSManager.trail (fn () =>
                          eq (G, UsVs1', UsVs') andalso sc ()
                          andalso ltAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic))
         orelse
         CSManager.trail (fn () =>
                          eq (G, UsVs1, UsVs') andalso sc ()
                          andalso ltAtomicR (GQ, (D @ D'), UsVs, UsVs1', sc, atomic))
         orelse
         transLt (GQ, D, (Eq(UsVs1, UsVs1') :: D'), UsVs, UsVs', sc)
     | transLt (GQ as (G,Q), (Less(UsVs1, UsVs1') :: D), D', UsVs, UsVs', sc) =
         CSManager.trail (fn () =>
                          eq (G, UsVs1', UsVs') andalso sc ()
                           andalso eqAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic))
         orelse
         CSManager.trail (fn () =>
                          eq (G, UsVs1', UsVs') andalso sc ()
                          andalso
                          ltAtomicR (GQ, (D @ D'), UsVs, UsVs1, sc, atomic))
         orelse
         transLt (GQ, D, (Less(UsVs1, UsVs1') :: D'), UsVs, UsVs', sc)


    (* atomic (GQ, D, P) = B

     An atomic order context D' is maximally decomposed iff

          T := Root(c, Nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   all atomic order relations in D' are
          either T' < T or T1' = T1'

   An atomic order P' is maximally decomposed iff
          T := Root(c, nil) | Root(n, Nil)
    and   T' := Root(c,S) | Root(n, S)
    and   T' < T or T1 = T1

    Invariant:

    B iff
          D and P are maximally decomposed,
      and they may contain EVars
      and G : Q
      and G |- P
      and G |- D
      and D --> P

      *)
    and atomic (GQ, D, D', Eq(UsVs, UsVs'), sc) =
         eqAtomic (GQ, D, D', UsVs, UsVs', sc)
      | atomic (GQ, D, D',Less(UsVs, UsVs'), sc) =
         ltAtomic (GQ, D, D', UsVs, UsVs', sc)

   (*-----------------------------------------------------------*)

   (* leftInstantiate ((G,Q), D, D', P, sc) = B

     B iff
           G : Q
       and G |- D
       and G |- D'
       and G |- P

       and  D is an atomic order relation ctx, which does not
              contain any EVars
       and  D' is an atomic order relation ctx, which may
              contain EVars
       and  P' is a atomic order relation

       and  D --> P

    D' accumulates all orders
    *)
    and leftInstantiate (GQ as (G, Q), nil, D', P, sc) =
          if atomic(GQ, D', nil, P, sc)
            then
              (if !Global.chatter > 4
                 then print (" Proved: " ^ atomicRCtxToString (G, D') ^
                             " ---> " ^ atomicPredToString (G, P)
                             ^ "\n")
               else (); true)
          else
            (* should never happen by invariant *)
             false

      | leftInstantiate (GQ, (Less(UsVs, UsVs') :: D), D', P, sc) =
          ltInstL (GQ, D, D', UsVs, UsVs', P, sc)
      | leftInstantiate (GQ, (Leq(UsVs, UsVs') :: D), D', P, sc) =
          leInstL (GQ, D, D', UsVs, UsVs', P, sc)
      | leftInstantiate (GQ, (Eq(UsVs, UsVs') :: D), D', P, sc) =
          eqInstL (GQ, D, D', UsVs, UsVs', P, sc)

    (* ltInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] < U'[s'] ---> P
    *)
    and ltInstL (GQ, D, D', UsVs, UsVs', P', sc) =
          ltInstLW (GQ, D, D', Whnf.whnfEta UsVs, UsVs', P', sc)

    and ltInstLW (GQ as (G, Q), D, D', ((I.Lam (Dec as I.Dec (_, V1), U), s1),
               (I.Pi ((I.Dec (_, V2), _), V), s2)), ((U', s1'), (V', s2')), P', sc) =
        if Subordinate.equiv (I.targetFam V', I.targetFam V1) (* == I.targetFam V2' *)
          then
            let
              val X = I.newEVar (G, I.EClo (V1, s1))
              (* = I.newEVar (I.EClo (V2', s2')) *)
              (* enforces that X can only bound to parameter or remain uninstantiated *)
              val sc' = fn () => (isParameter (Q, X) andalso sc ())
            in
              ltInstL ((G, Q), D, D',
                  ((U, I.Dot (I.Exp (X), s1)), (V, I.Dot (I.Exp (X), s2))),
                  ((U', s1'), (V', s2')), P', sc')
            end
        else
          if Subordinate.below  (I.targetFam V1, I.targetFam V')
            then
              let
                val X = I.newEVar (G, I.EClo (V1, s1))
                   (* = I.newEVar (I.EClo (V2', s2')) *)
              in
                ltInstL ((G, Q), D, D',
                     ((U, I.Dot (I.Exp (X), s1)),
                     (V, I.Dot (I.Exp (X), s2))),
                     ((U', s1'), (V', s2')), P', sc)
              end
          else false (* impossible, if additional invariant assumed (see ltW) *)
      | ltInstLW (GQ, D, D', UsVs, UsVs', P', sc) =
            leftInstantiate (GQ, D, (Less(UsVs, UsVs') :: D'), P', sc)


    (* leInstL ((G, Q), D, D', UsVs, UsVs', P', sc) = B
     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] contains EVars
       and  D, D', U[s1] <= U'[s'] ---> P'
    *)

    and leInstL (GQ, D, D', UsVs, UsVs', P', sc) =
          leInstLW (GQ, D, D', Whnf.whnfEta UsVs, UsVs', P', sc)


    and leInstLW (GQ as (G, Q), D, D', ((I.Lam (I.Dec (_, V1), U), s1),
               (I.Pi ((I.Dec (_, V2), _), V), s2)), ((U', s1'), (V', s2')), P', sc) =
        if Subordinate.equiv (I.targetFam V', I.targetFam V1) (* == I.targetFam V2' *)
          then
            let
              val X = I.newEVar (G, I.EClo (V1, s1))
              (* = I.newEVar (I.EClo (V2', s2')) *)
              (* enforces that X can only bound to parameter or remain uninstantiated *)
              val sc' = fn () => (isParameter (Q, X) andalso sc ())
            in
              leInstL ((G, Q), D, D',
                  ((U, I.Dot (I.Exp (X), s1)), (V, I.Dot (I.Exp (X), s2))),
                  ((U', s1'), (V', s2')), P', sc')
            end
        else
          if Subordinate.below  (I.targetFam V1, I.targetFam V')
            then
              let
                val X = I.newEVar (G, I.EClo (V1, s1))
                   (* = I.newEVar (I.EClo (V2', s2')) *)
              in
                leInstL ((G, Q), D, D',
                     ((U, I.Dot (I.Exp (X), s1)),
                     (V, I.Dot (I.Exp (X), s2))),
                     ((U', s1'), (V', s2')), P', sc)
              end
          else false (* impossible, if additional invariant assumed (see ltW) *)
      | leInstLW (GQ, D, D', UsVs, UsVs', P, sc) =
            leftInstantiate (GQ, D, (Less(UsVs, UsVs') :: D'), P, sc)



    (* eqInstL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
    *)

    and eqInstL (GQ, D, D', UsVs, UsVs', P', sc) =
          eqInstLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P', sc)

    and eqInstLW (GQ as (G,Q), D, D',
                  ((I.Lam (I.Dec (_, V1'), U'), s1'), (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
                  ((I.Lam (I.Dec (_, V1''), U''), s1''), (I.Pi ((I.Dec (_, V2''), _), V''), s2'')),
                  P', sc) =

           let
             val X = I.newEVar (G, I.EClo (V1'', s1''))
                (* = I.newEVar (I.EClo (V2', s2')) *)
           in
            eqInstL (GQ, D, D',
                     ((U', I.Dot (I.Exp(X), s1')),  (V', I.Dot(I.Exp(X), s2'))),
                     ((U'', I.Dot (I.Exp(X), s1'')),
                      (V'', I.Dot (I.Exp(X), s2''))), P',
                     fn () => (isParameter (Q, X); sc ()))
           end
       | eqInstLW (GQ, D, D', UsVs, UsVs', P', sc) =
          eqIL (GQ, D, D', UsVs, UsVs', P', sc)

    (* eqIL ((G, Q), D, D', UsVs, UsVs', P, sc) = B

     Invariant:
       B holds  iff
            G : Q
       and  D is an atomic order relation ctx
       and  D' is an atomic order relation ctx
       and  P' is a atomic order relation
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V [s2]
       and  G |- s' : G3  G3 |- U' : V'
       and  sc is a constraint continuation representing restrictions on EVars
       and  V[s2] atomic
       and  only U[s1] and U'[s'] contain EVars
       and  D, D', U[s1] = U'[s'] ---> P'
       and U, U' will be maximally unfolded
    *)

   and eqIL (GQ as (G, Q), D, D', UsVs as ((I.Root (I.Const c, S), s), Vs),
            UsVs' as ((I.Root (I.Const c', S'), s'), Vs'), P', sc) =
         if eqCid(c, c')
           then eqSpineIL (GQ, D, D', ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^ atomicRCtxToString (G, (Eq(UsVs, UsVs') :: D))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
            true)

     | eqIL (GQ as (G, Q), D, D', UsVs as ((I.Root (I.Def c, S), s), Vs),
            UsVs' as ((I.Root (I.Def c', S'), s'), Vs'), P', sc) =
         if eqCid(c, c')
           then eqSpineIL (GQ, D, D', ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^ atomicRCtxToString (G, (Eq(UsVs, UsVs') :: D))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
            true)

     | eqIL (GQ as (G, Q), D, D', (Us as (I.Root (I.Const c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), P', sc) =
         if isAtomic (GQ, Us')
           then leftInstantiate (GQ, D, (Eq((Us', Vs'),(Us, Vs)) :: D'), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^  atomicRCtxToString (G, (Eq((Us, Vs), (Us', Vs')) :: D))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
           true)

     | eqIL (GQ as (G, Q), D, D', (Us as (I.Root (I.Def c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), P', sc) =
         if isAtomic (GQ, Us')
           then leftInstantiate (GQ, D, (Eq((Us', Vs'),(Us, Vs)) :: D'), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^  atomicRCtxToString (G, (Eq((Us, Vs), (Us', Vs')) :: D))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
           true)

     | eqIL (GQ as (G, Q), D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Def c, S'), s'), Vs'), P', sc) =
         if isAtomic (GQ, Us)
           then leftInstantiate (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^  atomicRCtxToString (G, (Eq((Us, Vs), (Us', Vs')) :: D'))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
           true)


     | eqIL (GQ as (G, Q), D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Const c, S'), s'), Vs'), P', sc) =
         if isAtomic (GQ, Us)
           then leftInstantiate (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P', sc)
         else
           (if !Global.chatter > 4
              then print (" Proved: " ^  atomicRCtxToString (G, (Eq((Us, Vs), (Us', Vs')) :: D'))
                          ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                          ^ "\n")
            else ();
           true)

     | eqIL (GQ as (G, Q), D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.BVar n', S'), s'), Vs'), P', sc) =
             if (n = n')
               then
                 let
                   val I.Dec (_, V') = I.ctxDec (G, n)
                 in
                   eqSpineIL (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P', sc)
                 end
             else
               leftInstantiate (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P', sc)

     | eqIL (GQ as (G, Q), D, D', UsVs, UsVs', P', sc) =
        (* (Us, Vs as (I.Pi _ , _)) and (Us', Vs' as (I.Root _, _))
           or the other way
         *)
       (if !Global.chatter > 4
          then print (" Proved: " ^  atomicRCtxToString (G, (Eq((UsVs), (UsVs')) :: D))
                      ^ atomicRCtxToString (G, D') ^ " ---> " ^ atomicPredToString (G, P')
                      ^ "\n")
        else ();
          true)

    and eqSpineIL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P', sc) =
         eqSpineILW (GQ, D, D', (Ss, Whnf.whnf Vs), (Ss', Whnf.whnf Vs'), P', sc)

   and eqSpineILW (GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P', sc) =
        leftInstantiate (GQ, D, D', P', sc)
     | eqSpineILW (GQ, D, D', ((I.SClo(S, s'), s''), Vs), SsVs', P', sc) =
         eqSpineIL (GQ, D, D', ((S, I.comp (s', s'')), Vs), SsVs', P', sc)
     | eqSpineILW (GQ, D, D', SsVs, ((I.SClo(S', s'), s''), Vs'), P', sc) =
         eqSpineIL (GQ, D, D', SsVs, ((S', I.comp (s', s'')), Vs'), P', sc)
     | eqSpineILW (GQ, D, D', ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
                 ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), P', sc) =
         let
           val D1 = (Eq(((U,s1), (V1, s2)), ((U',s1'), (V1', s2'))) :: D)
         in
           eqSpineIL (GQ, D1, D', ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
                     ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), P', sc)
         end

   (*--------------------------------------------------------------*)

   (* rightDecompose (GQ, D', P) = B

    B iff
        G : Q
    and D is maximally unfolded, but does not contain any EVars
    and P is a order relation
    and G |- P
    and D --> P

    *)
   and rightDecompose (GQ, D', Less(O,O')) = ordLtR (GQ, D', O, O')
     | rightDecompose (GQ, D', Leq(O, O')) = ordLeR (GQ, D', O, O')
     | rightDecompose (GQ, D', Eq(O, O')) = ordEqR(GQ, D', O , O')


  (* ordLtR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 < O2
    *)

   and ordLtR (GQ, D', R.Arg UsVs, R.Arg UsVs') =
         ltAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
     | ordLtR (GQ, D', R.Lex O, R.Lex O') =
         ltLexR (GQ, D', O, O')

     | ordLtR (GQ, D', R.Simul O, R.Simul O') =
         ltSimulR (GQ, D', O, O')

  (* ordLeR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 <= O2
    *)

   and ordLeR (GQ, D', R.Arg UsVs, R.Arg UsVs') =
         leAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
     | ordLeR (GQ, D', R.Lex O, R.Lex O') =
         ltLexR (GQ, D', O, O')
         orelse
         ordEqsR (GQ, D', O, O')
     | ordLeR (GQ, D', R.Simul O, R.Simul O') =
         leSimulR (GQ, D', O, O')

  (* ordEqR (GQ, D, O1, O2) = B'

       Invariant:
       If   G : Q
       and  G |- O1 augmented subterm
       and  G |- O2 augmented subterm not containing any EVars
       then B' holds iff D --> O1 = O2
    *)
   and ordEqR (GQ, D', R.Arg UsVs, R.Arg UsVs') =
         conv (UsVs, UsVs')
         orelse
         eqAtomicR (GQ, D', UsVs, UsVs', init, leftInstantiate)
     | ordEqR (GQ, D', R.Lex O, R.Lex O') =
         ordEqsR (GQ, D', O, O')
     | ordEqR (GQ, D', R.Simul O, R.Simul O') =
         ordEqsR (GQ, D', O, O')

    (* ordEqsR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D' --> L1 = L2
    *)
   and ordEqsR (GQ, D', nil, nil)  = true
     | ordEqsR (GQ, D', O :: L, O' :: L') =
         ordEqR (GQ, D', O, O')
         andalso ordEqsR (GQ, D', L, L')

   (* ltLexR (GQ, D', L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D' --> L1 is lexically smaller than L2
    *)
   and ltLexR (GQ, D', nil, nil) = false
     | ltLexR (GQ, D', O :: L, O' :: L') =
         ordLtR (GQ, D', O, O')
         orelse
         (ordEqR (GQ, D', O, O') andalso ltLexR (GQ, D', L, L'))


   and leLexR (GQ, D', L, L') =
        ltLexR (GQ, D', L, L')
        orelse ordEqsR (GQ, D', L, L')


    (* ltSimulR (GQ, D, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not contianing any EVars
       then B' holds iff D implies that L1 is simultaneously smaller than L2
    *)
    and ltSimulR (GQ, D, nil, nil) = false
      | ltSimulR (GQ, D, O :: L, O' :: L') =
          (ordLtR (GQ, D, O, O') andalso leSimulR (GQ, D, L, L'))
          orelse
          (ordEqR (GQ, D, O, O') andalso ltSimulR (GQ, D, L, L'))

    (* leSimulR (G, Q, L1, L2) = B'

       Invariant:
       If   G : Q
       and  G |- L1 list of augmented subterms
       and  G |- L2 list of augmented subterms not containing any EVars
       then B' holds iff D implies that L1 is simultaneously less than or equal to L2
    *)
    and leSimulR (GQ, D, nil, nil) = true
      | leSimulR (GQ, D, O :: L, O' :: L') =
          ordLeR (GQ, D, O, O') andalso leSimulR (GQ, D, L, L')

   (*--------------------------------------------------------------*)
   (* Atomic Orders (Right) *)

    (* ltAtomicR (GQ, (D, D'), UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' implies U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)
   and ltAtomicR (GQ, D, UsVs, UsVs', sc, k) =
         ltAtomicRW (GQ, D, Whnf.whnfEta UsVs, UsVs', sc, k)

   and ltAtomicRW (GQ, D, UsVs as (Us, Vs as (I.Root _, s')), UsVs', sc, k) =
         ltR (GQ, D, UsVs, UsVs', sc, k)
     | ltAtomicRW (GQ as (G, Q), D, ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
                   ((U', s1'), (V', s2')), sc, k) =
        let
          val UsVs' = ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))
          val UsVs = ((U, I.dot1 s1), (V, I.dot1 s2))
          val D' = shiftACtx D (fn s => I.comp(s, I.shift))
        in
          ltAtomicR ((I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))),
                      I.Decl (Q, All)), D', UsVs, UsVs', sc, k)
        end


    (* leAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)

   and leAtomicR (GQ, D, UsVs, UsVs', sc, k) =
         leAtomicRW (GQ, D, Whnf.whnfEta UsVs, UsVs', sc, k)

   and leAtomicRW (GQ, D, UsVs as (Us, Vs as (I.Root _, s')), UsVs', sc, k) =
         leR (GQ, D, UsVs, UsVs', sc, k)
     | leAtomicRW (GQ as (G, Q), D, ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
                   ((U', s1'), (V', s2')), sc, k) =
        let
          val D' = shiftACtx D (fn s => I.comp(s, I.shift))
          val UsVs' = ((U', I.comp (s1', I.shift)), (V', I.comp (s2', I.shift)))
          val UsVs = ((U, I.dot1 s1), (V, I.dot1 s2))
        in
          leAtomicR ((I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))),
                      I.Decl (Q, All)), D', UsVs, UsVs', sc, k)
        end


    (* eqAtomicR (GQ, D, UsVs, UsVs', sc, k) = B
     Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D implies U[s1] is structurally equivalent to U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded
    *)

   and eqAtomicR (GQ as (G, Q), D, UsVs, UsVs', sc, k) =
        eqAtomicRW (GQ, D, Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', sc, k)

   and eqAtomicRW (GQ as (G, Q), D, ((I.Lam (_, U), s1), (I.Pi ((Dec, _), V), s2)),
                   ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')), sc, k) =
       (* Dec = Dec' *)
         eqAtomicR ((I.Decl (G, N.decLUName (G, I.decSub (Dec, s2))), I.Decl (Q, All)),
                    shiftACtx D (fn s => I.comp(s, I.shift)),
                    ((U, I.dot1 s1'), (V, I.dot1 s2')),
                    ((U', I.dot1 s1'),(V', I.dot1 s2')), sc, k)
     | eqAtomicRW (GQ, D, (Us, Vs as (I.Root _, s2)),(Us', Vs' as (I.Root _, s2')), sc, k) =
         eqR (GQ, D, (Us, Vs),(Us', Vs'), sc, k)
     | eqAtomicRW (GQ, D, (Us, Vs), (Us', Vs'),sc, k) =
         (* mismatch: not equal *)
         (* Fri Feb 25 21:26:39 2005 -fp !!! *)
         false

   (* ltR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a strict subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
       and k is a continuation describing what happens when
           UsVs and UsVs' are maximally unfolded

    *)
  and ltR (GQ as (G, Q), D, UsVs, UsVs', sc, k) =
        ltRW (GQ, D, UsVs, Whnf.whnfEta UsVs', sc, k)

  and ltRW (GQ, D, (Us, Vs), (Us' as (I.Root (I.Const c, S'), s'), Vs'), sc, k) =
        if isAtomic (GQ, Us')
          then k (GQ, D, nil, Less((Us,Vs), (Us', Vs')), sc)
               (* either leftInstantiate D or  atomic reasoning *)
        else
          ltSpineR (GQ, D, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, k)

    | ltRW (GQ, D, (Us, Vs), (Us' as (I.Root (I.Def c, S'), s'), Vs'), sc, k) =
        if isAtomic (GQ, Us')
          then k (GQ, D, nil, Less((Us,Vs), (Us', Vs')), sc)
               (* either leftInstantiate D or  atomic reasoning *)
        else
          ltSpineR (GQ, D, (Us, Vs), ((S', s'), (I.constType c, I.id)), sc, k)

    | ltRW (GQ as (G, Q), D, (Us, Vs), (Us' as (I.Root (I.BVar n, S'), s'), Vs'), sc, k) =
        if isAtomic (GQ, Us')
          then k (GQ, D, nil, Less((Us,Vs), (Us', Vs')), sc)
               (* either leftInstantiate D or  atomic reasoning *)
        else
          let
            val I.Dec (_, V') = I.ctxDec (G, n)
          in
            ltSpineR (GQ, D, (Us, Vs), ((S', s'), (V', I.id)), sc, k)
          end

      | ltRW (GQ, D, _, ((I.EVar _, _), _), _, _) = false

      | ltRW (GQ as (G, Q), D, ((U, s1), (V, s2)),
              ((I.Lam (I.Dec (_, V1'), U'), s1'),
               (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, k) =
          if Subordinate.equiv (I.targetFam V, I.targetFam V1')
            (* == I.targetFam V2' *)
            then
              let  (* enforce that X is only instantiated to parameters *)
                val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
                val sc' = fn () => (isParameter (Q, X); sc ())
              in
                ltR (GQ, D, ((U, s1), (V, s2)),
                     ((U', I.Dot (I.Exp (X), s1')),
                      (V', I.Dot (I.Exp (X), s2'))), sc', k)
              end
          else
            if Subordinate.below (I.targetFam V1', I.targetFam V)
              then
                let
                  val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
                in
                  ltR (GQ, D, ((U, s1), (V, s2)),
                       ((U', I.Dot (I.Exp (X), s1')),
                        (V', I.Dot (I.Exp (X), s2'))), sc, k)
                end
            else false  (* possibly redundant if lhs always subordinate to rhs *)


    and ltSpineR (GQ, D, (Us, Vs), (Ss', Vs'), sc, k) =
          ltSpineRW (GQ, D, (Us, Vs), (Ss', Whnf.whnf Vs'), sc, k)

    and ltSpineRW (GQ, D, (Us, Vs), ((I.Nil, _), _), _, _) =
          (* cannot happen Sat Apr 20 16:08:30 2002 -bp *)
          false
      | ltSpineRW (GQ, D, (Us, Vs), ((I.SClo (S, s'), s''), Vs'), sc, k) =
          ltSpineR (GQ, D, (Us, Vs), ((S, I.comp (s', s'')), Vs'), sc, k)
      | ltSpineRW (GQ, D, (Us, Vs), ((I.App (U', S'), s1'),
                                      (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, k) =
          leAtomicR (GQ, D, (Us, Vs), ((U', s1'), (V1', s2')), sc, k) orelse
          ltSpineR (GQ, D, (Us, Vs),
                    ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, k)

   (* leR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] is a subterm of U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)

  and leR (GQ, D, UsVs, UsVs', sc, k) =

        leRW (GQ, D, UsVs, Whnf.whnfEta UsVs', sc, k)
   and leRW (GQ as (G, Q), D, ((U, s1), (V, s2)),
             ((I.Lam (I.Dec (_, V1'), U'), s1'),
              (I.Pi ((I.Dec (_, V2'), _), V'), s2')), sc, k) =
        if Subordinate.equiv (I.targetFam V, I.targetFam V1') (* == I.targetFam V2' *)
          then
            let
              val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
              (* enforces that X can only bound to parameter or remain uninstantiated *)
              val sc' = fn () => (isParameter (Q, X) andalso sc ())
            in
              leR (GQ, D, ((U, s1), (V, s2)),
                  ((U', I.Dot (I.Exp (X), s1')),
                   (V', I.Dot (I.Exp (X), s2'))), sc', k)
            end
        else
          if Subordinate.below  (I.targetFam V1', I.targetFam V)
            then
              let
                val X = I.newEVar (G, I.EClo (V1', s1')) (* = I.newEVar (I.EClo (V2', s2')) *)
              in
                leR (GQ, D, ((U, s1), (V, s2)),
                    ((U', I.Dot (I.Exp (X), s1')),
                     (V', I.Dot (I.Exp (X), s2'))), sc, k)
              end
          else false (* impossible, if additional invariant assumed (see ltW) *)

      | leRW (GQ, D, UsVs, UsVs', sc, k) =
          ltR (GQ, D, UsVs, UsVs', sc, k)
          orelse
          eqR (GQ, D, UsVs, UsVs', sc, k)


   (* eqR (GQ, D, UsVs, UsVs', sc, k) = B

       Invariant:
       B' holds  iff
            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']
       and  D' --> U[s1] = U'[s1']
       and  sc is a constraint continuation representing restrictions on EVars
       and only U'[s'] contains EVars
       and U'[s'] will be maximally unfolded
    *)
  and eqR (GQ as (G, Q), D, UsVs, UsVs', sc, k) =
         CSManager.trail (fn () => eq (G, UsVs, UsVs') andalso sc ())
         orelse
         eqR' (GQ, D, UsVs, UsVs', sc, k)


   and eqR' (GQ, D,(Us, Vs as (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
            (Us', Vs' as (I.Root _, s2'')), sc, k) =
        false
     | eqR' (GQ, D,(Us, Vs as (I.Root _, s2')),
            (Us', Vs' as (I.Pi ((I.Dec (_, V2''), _), V''), s2'')), sc, k) =
        false

     | eqR' (GQ, D, UsVs as ((I.Root (I.Const c, S), s), Vs),
            UsVs' as ((I.Root (I.Const c', S'), s'), Vs'), sc, k) =
         if eqCid(c, c')
           then eqSpineR (GQ, D, ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), sc, k)
         else
           false

     | eqR' (GQ, D, (Us as (I.Root (I.Const c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), sc, k) =
         if isAtomic (GQ, Us')
           then k (GQ, D, nil, Eq((Us', Vs'),(Us, Vs)), sc)
                (* either leftInstantiate D or atomic reasoning *)

         else
           false

     | eqR' (GQ, D, (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Const c, S'), s'), Vs'), sc, k) =
         if isAtomic (GQ, Us)
           then k (GQ, D, nil, Eq((Us, Vs),(Us', Vs')), sc)
                (* either leftInstantiate D or atomic reasoning *)
         else
           false

     | eqR' (GQ, D, UsVs as ((I.Root (I.Def c, S), s), Vs),
            UsVs' as ((I.Root (I.Def c', S'), s'), Vs'), sc, k) =
         if eqCid(c, c')
           then eqSpineR (GQ, D, ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), sc, k)
         else
           false

     | eqR' (GQ, D, (Us as (I.Root (I.Def c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), sc, k) =
         if isAtomic (GQ, Us')
           then k (GQ, D, nil, Eq((Us', Vs'),(Us, Vs)), sc)
                (* either leftInstantiate D or atomic reasoning *)

         else
           false

     | eqR' (GQ, D, (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Def c, S'), s'), Vs'), sc, k) =
         if isAtomic (GQ, Us)
           then k (GQ, D, nil, Eq((Us, Vs),(Us', Vs')), sc)
                (* either leftInstantiate D or atomic reasoning *)
         else
           false

     | eqR' (GQ as (G, Q), D, (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.BVar n', S'), s'), Vs'), sc, k) =
         if (n = n')
           then
             let
               val I.Dec (_, V') = I.ctxDec (G, n)
             in
               eqSpineR (GQ, D, ((S, s), (V', I.id)), ((S', s'), (V', I.id)), sc, k)
             end
         else
           k (GQ, D, nil, Eq((Us, Vs), (Us', Vs')), sc)
           (* either leftInstantiate D or atomic reasoning *)

     (* UsVs = Lam *)
     | eqR' (GQ, D, UsVs, UsVs', sc, k) =
           k (GQ, D, nil, Eq(UsVs, UsVs'), sc)
           (* either leftInstantiate D or atomic reasoning *)


   and eqSpineR (GQ, D, (Ss, Vs), (Ss', Vs'), sc, k) =
         eqSpineRW (GQ, D, (Ss, (Whnf.whnf Vs)), (Ss', (Whnf.whnf Vs')), sc, k)

   and eqSpineRW (GQ, D, ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), sc, k) =
        true
     | eqSpineRW (GQ, D, ((I.SClo(S, s'), s''), Vs), SsVs', sc, k) =
         eqSpineR (GQ, D, ((S, I.comp (s', s'')), Vs), SsVs', sc, k)
     | eqSpineRW (GQ, D, SsVs, ((I.SClo(S', s'), s''), Vs'), sc, k) =
         eqSpineR (GQ, D, SsVs, ((S', I.comp (s', s'')), Vs'), sc, k)
     | eqSpineRW (GQ, D, ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
                 ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), sc, k) =
           eqAtomicR (GQ, D, ((U, s1), (V1, s2)), ((U',s1'), (V1', s2')), sc, k)
           andalso
           eqSpineR (GQ, D, ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
                     ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), sc, k)
     | eqSpineRW (GQ, D, SsVs, SsVs', sc, k) = false

   (*--------------------------------------------------------------*)
   (* leftDecompose (G, Q, D, D', P) = B

      if G : Q and
         D --> P  where D might contain orders (lex and simul)

      then D' --> P
           where all orders in D' are atomic

      D' accumulates all orders which are maximally unfolded,
      but do not contain any EVars

      maximally unfolded orders not containing EVars are:

      Less: R < L

      L := Root(c, Nil) | Root(n, Nil)
      R := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)


      Eq : R = L
      R := Root(n, Nil) | Lam(x:A, R)
      L := Root(c, S) | Root(n, S) | Lam(x:A, R)
      S := . | App(R, S)

    *)

   fun leftDecompose (GQ as (G, Q), nil, D', P) =
         rightDecompose (GQ, D', P)
     (* less *)
     | leftDecompose (GQ, (Less(R.Arg UsVs, R.Arg UsVs') :: D), D', P) =
          ltAtomicL (GQ, D, D', UsVs, UsVs', P)

     | leftDecompose (GQ, (Less(R.Lex O, R.Lex O') :: D), D', P) =
         ltLexL (GQ, D, D', O, O', P)

     | leftDecompose (GQ, (Less(R.Simul O, R.Simul O') :: D), D', P) =
         ltSimulL (GQ, D, D', O, O', P)
     (* le *)
     | leftDecompose (GQ, (Leq(R.Arg UsVs, R.Arg UsVs') :: D), D', P) =
         leAtomicL (GQ, D, D', UsVs, UsVs', P)

     | leftDecompose (GQ, (Leq(R.Lex O, R.Lex O') :: D), D', P) =
         leftDecompose (GQ, (Less(R.Lex O, R.Lex O') :: D), D', P)
         andalso
         leftDecompose (GQ, (Eq(R.Lex O, R.Lex O') :: D), D', P)

     | leftDecompose (GQ, (Leq(R.Simul O, R.Simul O') :: D), D', P) =
         leSimulL (GQ, D, D', O, O', P)
     (* eq *)
     | leftDecompose (GQ, (Eq(R.Arg UsVs, R.Arg UsVs') :: D), D', P) =
         eqAtomicL (GQ, D, D', UsVs,  UsVs', P)

     | leftDecompose (GQ, (Eq(R.Lex O, R.Lex O') :: D), D', P) =
         eqsL (GQ, D, D', O, O', P)

     | leftDecompose (GQ, (Eq(R.Simul O, R.Simul O') :: D), D', P) =
         eqsL (GQ, D, D', O, O', P)

     | leftDecompose (GQ as (G, Q), (Pi(Dec, O) :: D), D', P) =
         (* drop assumption Pi D. P *)
         ((if !Global.chatter > 3
                 then (print " Ignoring quantified order ";
                      print (F.makestring_fmt(fmtPredicate (G, Pi(Dec, O)))))
          else ());
         leftDecompose (GQ, D, D', P))


   (*--------------------------------------------------------------*)
   (* Lexicographic and Simultanous Orders (left)*)


   (* If D, D', Lex O1, ....On < Lex O'1, ....O'n --> P
      then
            D, D', O1 < O1' --> P
        and D, D', O1 = O1', O2 < O2 --> P

        ...
        and D, D', O1 = O1', .., O_n-1 = O'_n-1, O_n < O'_n --> P
    *)
   and ltLexL (GQ, D, D', nil, nil, P) = true
     | ltLexL (GQ, D, D', O :: L, O' :: L', P) =
         leftDecompose(GQ, (Less(O, O') :: D), D', P)
         andalso
         ltLexL(GQ, (Eq(O, O') :: D), D', L, L', P)


   (* If D, D', Lex O1, ....On = Lex O'1, ....O'n --> P
      If D, D', Simul O1, ....On = Simul O'1, ....O'n --> P
      then
            D, D', O1 = O1' --> P
        and D, D', O2 = O2' --> P

        ...
        and D, D', On = On' --> P
    *)
   and eqsL (GQ, D, D', nil, nil, P) = true
     | eqsL (GQ, D, D', O :: L, O' :: L', P) =
         leftDecompose(GQ, (Eq(O, O') :: D), D', P)
         andalso
         eqsL(GQ, D, D', L, L', P)


   and ltSimulL (GQ, D, D', nil, nil, P) =
         leftDecompose (GQ, D, D', P)
     | ltSimulL (GQ, D, D', O :: L, O' ::L', P) =
         leSimulL (GQ, (Less(O, O') :: D), D', L, L', P)
         orelse
         ltSimulL(GQ, (Eq(O, O') :: D), D', L, L', P)

   and leSimulL (GQ, D, D', nil, nil, P) =
         leftDecompose (GQ, D, D', P)
     | leSimulL (GQ, D, D', O :: L, O' :: L', P) =
         leSimulL (GQ, (Leq(O, O') :: D), D', L, L', P)

   (*--------------------------------------------------------------*)
   (* Atomic Orders (left) *)

   (* U := Root(c, S) | Root(n, S) | Lam(x:A, U) *)


   (* ltAtomicL (GQ as (G, Q), D, D', ((U, s1), (V, s2)), ((U', s1'), (V', s2')), P) = B

     B holds iff

            G : Q
       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and  G |- D, D', (U[s1]:V[s2]) < U'[s1']:V'[s2']) --> P


       if G |- D, D', (Us:Vs) < (\x1:A1....\xn:An. U'[s1']: V'[s2']) --> P and
               (n >= 0)
       then
          G, a1:A1, .... an:An |-
             D^n, D'^n, (Us^n:Vs^n) < U'[a1... an . s1'^n]:V'[a1. ... . an . s2'^n] --> P^n

       where D^n, (Us^n, P^n) means all substitutions in D (U, P etc)
             are shifted by n
    *)
   and ltAtomicL (GQ, D, D', UsVs, UsVs', P) =
         ltAtomicLW (GQ, D, D', UsVs, Whnf.whnfEta UsVs', P)

   and ltAtomicLW (GQ as (G,Q), D, D', UsVs, (Us', Vs' as (I.Root _, s')), P) =
         ltL (GQ, D, D', UsVs, (Us', Vs'), P)
     | ltAtomicLW (GQ as (G, Q), D, D', ((U, s1), (V, s2)),
                  ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')), P) =
        let
          val D1 = shiftRCtx D (fn s => I.comp(s, I.shift))
          val D1' = shiftACtx D' (fn s => I.comp(s, I.shift))
          val UsVs = ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift)))
          val UsVs' = ((U', I.dot1 s1'), (V', I.dot1 s2'))
          val P' = shiftP P (fn s => I.comp(s, I.shift))
        in
          ltAtomicL ((I.Decl (G, N.decLUName (G, I.decSub (Dec', s2'))), I.Decl (Q, All)),
                     D1, D1', UsVs, UsVs' ,  P')
        end

   (* see invariant for ltAtomic *)
   and leAtomicL (GQ, D, D', UsVs, UsVs', P) =
         leAtomicLW (GQ, D, D', UsVs, Whnf.whnfEta UsVs', P)

   and leAtomicLW (GQ, D, D', UsVs, (Us', Vs' as (I.Root (H,S), s')), P) =
        leL (GQ, D, D', UsVs, (Us', Vs'), P)
     | leAtomicLW (GQ as (G, Q), D, D', ((U, s1), (V, s2)),
                  ((I.Lam (_, U'), s1'), (I.Pi ((Dec', _), V'), s2')), P) =
        let
          val D1 = shiftRCtx D (fn s => I.comp(s, I.shift))
          val D1' = shiftACtx D' (fn s => I.comp(s, I.shift))
          val UsVs = ((U, I.comp (s1, I.shift)), (V, I.comp (s2, I.shift)))
          val UsVs' = ((U', I.dot1 s1'), (V', I.dot1 s2'))
          val P' = shiftP P (fn s => I.comp(s, I.shift))
        in
          leAtomicL ((I.Decl (G, N.decLUName (G, I.decSub (Dec', s2'))), I.Decl (Q, All)),
                     D1, D1', UsVs, UsVs' , P')
        end

   (*  *)
   and eqAtomicL (GQ, D, D', UsVs, UsVs', P) =
         eqAtomicLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P)

   and eqAtomicLW (GQ, D, D', (Us, Vs as (I.Root _, s)),
                               (Us', Vs' as (I.Root _, s')), P) =
        eqL (GQ, D, D', (Us, Vs), (Us', Vs'), P)
     | eqAtomicLW (GQ, D, D', (Us, Vs as (I.Root _, s)), (Us', Vs' as (I.Pi _, s')), P) = true
     | eqAtomicLW (GQ, D, D', (Us, Vs as (I.Pi _, s)), (Us', Vs' as (I.Root _, s')), P) = true
     | eqAtomicLW (GQ, D, D', (Us, Vs as (I.Pi _, s)), (Us', Vs' as (I.Pi _, s')), P) =
        leftDecompose(GQ, D, (Eq((Us,Vs), (Us', Vs')) :: D'), P)


   (*--------------------------------------------------------------*)
   (* U' := Root(c, S) | Root(n, S) *)
   (* add definitions! *)

   and leL (GQ, D, D', UsVs, UsVs', P) =
         ltAtomicL (GQ, D, D', UsVs, UsVs', P)
         andalso
         eqAtomicL (GQ, D, D', UsVs, UsVs', P)


   (*  If D, D', U < Root(c, S) --> P
      then D, D', U <= S' --> P
   *)
   and ltL (GQ, D, D', UsVs, (Us', Vs'), P) =
        ltLW (GQ, D, D', UsVs, (Whnf.whnf Us', Vs'), P)

   and  ltLW (GQ as (G, Q), D, D', UsVs, (Us' as (I.Root (I.BVar n, S'), s'), Vs'), P) =
         if isAtomic(GQ, Us')
            then leftDecompose (GQ, D, (Less(UsVs, (Us',Vs')) :: D'), P)
          else
            let
              val I.Dec (_, V') = I.ctxDec (G, n)
            in
              ltSpineL (GQ, D, D', UsVs, ((S', s'), (V', I.id)), P)
            end
      | ltLW (GQ, D, D', UsVs, ((I.Root (I.Const c, S'), s'), Vs'), P) =
         ltSpineL (GQ, D, D', UsVs, ((S', s'), (I.constType c, I.id)), P)

      | ltLW (GQ, D, D', UsVs, ((I.Root (I.Def c, S'), s'), Vs'), P) =
         ltSpineL (GQ, D, D', UsVs, ((S', s'), (I.constType c, I.id)), P)

    and ltSpineL (GQ, D, D', UsVs, (Ss', Vs'), P) =
          ltSpineLW (GQ, D, D', UsVs, (Ss', Whnf.whnf Vs'), P)

    and ltSpineLW (GQ, D, D', UsVs, ((I.Nil, _), _), _) = true
      | ltSpineLW (GQ, D, D', UsVs, ((I.SClo (S, s'), s''), Vs'), P) =
          ltSpineL (GQ, D, D', UsVs, ((S, I.comp (s', s'')), Vs'), P)
      | ltSpineLW (GQ, D, D', UsVs, ((I.App (U', S'), s1'),
                                   (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), P) =
            leAtomicL (GQ, D, D', UsVs, ((U', s1'), (V1', s2')), P)
            andalso
            ltSpineL (GQ, D, D', UsVs,
                      ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), P)

  (*  eqL (GQ, D, D', UsVs, UsVs', P) = B

       B holds iff

            G : Q

       and  D is an Order relation ctx
       and  D' is an atomic order relation ctx
       and  P is a order relation

       and  G |- s1 : G1   G1 |- U : V1
       and  G |- s2 : G2   G2 |- V : L
       and  G |- U[s1] : V[s2]
       and  G |- s1' : G3   G3 |- U' : V1'
       and  G |- s2' : G4   G4 |- V' : L
       and  G |- U'[s1'] : V'[s2']

       and D, D', U[s1] = U'[s1'] --> P

       note: D, D', UsVs, UsVs' and P do not
             contain any EVars
   *)


  and eqL (GQ, D, D', UsVs, UsVs', P) =
       eqLW (GQ, D, D', Whnf.whnfEta UsVs, Whnf.whnfEta UsVs', P)

  and eqLW (GQ, D, D',(Us, Vs as (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
            (Us', Vs' as (I.Pi ((I.Dec (_, V2''), _), V''), s2'')), P) =
        leftDecompose (GQ, D, (Eq((Us,Vs), (Us', Vs')) :: D'), P)

    | eqLW (GQ, D, D',(Us, Vs as (I.Pi ((I.Dec (_, V2'), _), V'), s2')),
            (Us', Vs' as (I.Root _, s2'')), P) =
        true
    | eqLW (GQ, D, D',(Us, Vs as (I.Root _, s2')),
            (Us', Vs' as (I.Pi ((I.Dec (_, V2''), _), V''), s2'')), P) =
        true
    | eqLW (GQ, D, D', UsVs as ((I.Root (I.Const c, S), s), Vs),
            UsVs' as ((I.Root (I.Const c', S'), s'), Vs'), P) =
         if eqCid(c, c')
           then eqSpineL (GQ, D, D', ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), P)
         else
           true

     | eqLW (GQ, D, D', (Us as (I.Root (I.Const c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), P) =
         if isAtomic (GQ, Us')
           then leftDecompose (GQ, D, (Eq((Us', Vs'),(Us, Vs)) :: D'), P)
         else
           true

     | eqLW (GQ, D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Const c, S'), s'), Vs'), P) =
         if isAtomic (GQ, Us)
           then leftDecompose (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P)
         else
           true

    | eqLW (GQ, D, D', UsVs as ((I.Root (I.Def c, S), s), Vs),
            UsVs' as ((I.Root (I.Def c', S'), s'), Vs'), P) =
         if eqCid(c, c')
           then eqSpineL (GQ, D, D', ((S, s), (I.constType c, I.id)),
                         ((S', s'), (I.constType c', I.id)), P)
         else
           true

     | eqLW (GQ, D, D', (Us as (I.Root (I.Def c, S), s), Vs),
            (Us' as (I.Root (I.BVar n, S'), s'), Vs'), P) =
         if isAtomic (GQ, Us')
           then leftDecompose (GQ, D, (Eq((Us', Vs'),(Us, Vs)) :: D'), P)
         else
           true

     | eqLW (GQ, D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.Def c, S'), s'), Vs'), P) =
         if isAtomic (GQ, Us)
           then leftDecompose (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P)
         else
           true

(*
     | eqLW (GQ, D, D', UsVs as ((I.Root (I.BVar n, I.Nil), s), Vs),
            UsVs' as ((I.Root (I.BVar n', I.Nil), s'), Vs'), P) =
         if (n = n')
           then leftDecompose (GQ, D, D', P)
         else
           leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

*)
     | eqLW (GQ as (G, Q), D, D', (Us as (I.Root (I.BVar n, S), s), Vs),
            (Us' as (I.Root (I.BVar n', S'), s'), Vs'), P) =
         if (n = n')
           then
             let
               val I.Dec (_, V') = I.ctxDec (G, n)
             in
               eqSpineL (GQ, D, D', ((S, s), (V', I.id)), ((S', s'), (V', I.id)), P)
             end
         else
           leftDecompose (GQ, D, (Eq((Us, Vs), (Us', Vs')) :: D'), P)
     (* UsVs = Lam *)
     | eqLW (GQ, D, D', UsVs, UsVs', P) =
         leftDecompose (GQ, D, (Eq(UsVs, UsVs') :: D'), P)

    and eqSpineL (GQ, D, D', (Ss, Vs), (Ss', Vs'), P) =
         eqSpineLW (GQ, D, D', (Ss, Whnf.whnf Vs), (Ss', Whnf.whnf Vs'), P)

   and eqSpineLW (GQ, D, D', ((I.Nil, s), Vs), ((I.Nil, s'), Vs'), P) =
        leftDecompose (GQ, D, D', P)
     | eqSpineLW (GQ, D, D', ((I.SClo(S, s'), s''), Vs), SsVs', P) =
         eqSpineL (GQ, D, D', ((S, I.comp (s', s'')), Vs), SsVs', P)
     | eqSpineLW (GQ, D, D', SsVs, ((I.SClo(S', s'), s''), Vs'), P) =
         eqSpineL (GQ, D, D', SsVs, ((S', I.comp (s', s'')), Vs'), P)
     | eqSpineLW (GQ, D, D', ((I.App (U, S), s1), (I.Pi ((I.Dec (_, V1), _), V2), s2)),
                 ((I.App (U', S'), s1'), (I.Pi ((I.Dec (_, V1'), _), V2'), s2')), P) =
         let
           val D1 = (Eq(R.Arg ((U,s1), (V1, s2)), R.Arg ((U',s1'), (V1', s2'))) :: D)
         in
           eqSpineL (GQ, D1, D', ((S, s1), (V2, I.Dot (I.Exp (I.EClo (U, s1)), s2))),
                     ((S', s1'), (V2', I.Dot (I.Exp (I.EClo (U', s1')), s2'))), P)
         end

   (*--------------------------------------------------------------*)
   (* Infer: D --> P *)

    (* deduce (G, Q, D, P) = B

      B iff
         G :  Q
     and G |- D
     and G |- P
     and D implies P
    *)
    fun deduce (G, Q, D, P) = leftDecompose((G, Q), D, nil, P)
  in
    val deduce = deduce
    val shiftRCtx = shiftRCtx
    val shiftPred = shiftP
  end (* local *)
end; (* functor checking  *)
