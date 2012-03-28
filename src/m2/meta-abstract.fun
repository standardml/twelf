(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

functor MetaAbstract (structure Global : GLOBAL
                      structure MetaSyn' : METASYN
                      structure MetaGlobal : METAGLOBAL
                      structure Abstract : ABSTRACT
                      (*! sharing Abstract.IntSyn = MetaSyn'.IntSyn !*)
                      structure ModeTable : MODETABLE
                      (*! sharing ModeSyn.IntSyn = MetaSyn'.IntSyn !*)
                      structure Whnf : WHNF
                      (*! sharing Whnf.IntSyn = MetaSyn'.IntSyn !*)
                      structure Print : PRINT
                      (*! sharing Print.IntSyn = MetaSyn'.IntSyn !*)
                      structure Constraints : CONSTRAINTS
                      (*! sharing Constraints.IntSyn = MetaSyn'.IntSyn !*)
                      structure Unify : UNIFY
                      (*! sharing Unify.IntSyn = MetaSyn'.IntSyn !*)
                      structure Names : NAMES
                      (*! sharing Names.IntSyn = MetaSyn'.IntSyn !*)
                      structure TypeCheck : TYPECHECK
                      (*! sharing TypeCheck.IntSyn = MetaSyn'.IntSyn !*)
                      structure Subordinate : SUBORDINATE
                      (*! sharing Subordinate.IntSyn = MetaSyn'.IntSyn  !*)
                        )
  : METAABSTRACT =
struct
  structure MetaSyn = MetaSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure S = Stream
    structure M = MetaSyn
    structure C = Constraints

    (* Invariants? *)

    (* Definition: Mode dependency order

       A pair ((G, M), V) is in mode dependency order iff
           G |- V : type
           G |- M modes
       and G = G0+, G1-, G1+,  ... G0-
       and V = {xn:Vn} ..{x1:V1}P0
       where G0+ collects all +variables when traversing P0 in order
       and Gi+ collects all +variables when traverseing Vi in order  (i > 0)
       and Gi- collects all -variables when traversing Vi in order   (i > 0)
       and G0- collects all -variables when traversing P0 in order.
    *)

    datatype Var =                      (* Variable found during collect  *)
      EV of I.Exp option ref            (* Var ::= EVar <r_, V, St>       *)
      * I.Exp * MetaSyn.Mode
    | BV                                (*       | BV                     *)

    (*--------------------------------------------------------------------*)
    (* First section: Collecting EVars and BVars in mode dependency order *)
    (*--------------------------------------------------------------------*)

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    fun checkEmpty (nil) = ()
      | checkEmpty (Cnstr) =
        (case C.simplify Cnstr
           of nil => ()
            | _ => raise Error "Unresolved constraints")

    (* Let G x A: defined as

       .      x .            = .
       (G, V) x (A, BVar)    = (G x A), V
       (G, V) x (A, EVar V') = (G, V x A), V'

       Then all A : Atx satisfy the following invariant: |- A Atx

       ? If    A = A', EV (r, V, m)
       ? then  . |- V = {G x A'}.V' : type
       ? where G x A' |- V' : type

       We write A ||- U if all EVars and BVars of U are collected in A,
       A ||- S if all EVars and BVars of S are collected in A,
       and similiar notation for the other syntactic categories.
    *)

    (* typecheck ((G, M), V) = ()

       Invariant:
       If G |- V : type
       then typecheck returns ()
       else TypeCheck.Error is raised
    *)
    fun typecheck (M.Prefix (G, M, B), V) = TypeCheck.typeCheck (G, (V, I.Uni I.Type))

    (* modeEq (marg, st) = B'

       Invariant:
       If   (marg = + and st = top) or (marg = - and st = bot)
       then B' = true
       else B' = false
    *)
    fun modeEq (ModeSyn.Marg (ModeSyn.Plus, _), M.Top) = true
      | modeEq (ModeSyn.Marg (ModeSyn.Minus, _), M.Bot) = true
      | modeEq _ = false

    (* atxLookup (atx, r)  = Eopt'

       Invariant:
       If   r exists in atx as EV (V)
       then Eopt' = SOME EV and . |- V : type
       else Eopt' = NONE
    *)
    fun atxLookup (I.Null, _) = NONE
      | atxLookup (I.Decl (M, BV), r) = atxLookup (M, r)
      | atxLookup (I.Decl (M, E as EV (r', _, _)), r) =
        if (r = r') then SOME E
        else atxLookup (M, r)

    (* raiseType (k, G, V) = {{G'}} V

       Invariant:
       If G |- V : L
          G = G0, G'  (so k <= |G|)
       then  G0 |- {{G'}} V : L
             |G'| = k

       All abstractions are potentially dependent.
    *)
    fun raiseType (0, G, V) = V
      | raiseType (depth, I.Decl (G, D), V) =
          raiseType (depth-1, G, I.Pi ((D, I.Maybe), V))

    (* weaken (depth,  G, a) = (w')
    *)
    fun weaken (0, G, a) = I.id
      | weaken (depth, I.Decl (G', D as I.Dec (name, V)), a) =
        let
          val w' = weaken (depth-1, G', a)
        in
          if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end

    (* countPi V = n'

       If   G |- x : V
       and  V = {G'} V'
       then |G'| = n'
    *)
    (* V in nf or enf? -fp *)
    fun countPi V =
        let
          fun countPi' (I.Root _, n) = n
            | countPi' (I.Pi (_, V), n) = countPi' (V, n+1)
            | countPi' (I.EClo (V, _), n) = countPi' (V, n)
        in
          countPi' (V, 0)
        end

    (* collectExp (lG0, G, (U, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- U : V
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- U [s]
    *)
    fun collectExp (lG0, G, Us, mode, Adepth) =
          collectExpW (lG0, G, Whnf.whnf Us, mode, Adepth)

    and collectExpW (lG0, G, (I.Uni _, s), mode, Adepth) = (* impossible? *)
          Adepth
      | collectExpW (lG0, G, (I.Pi ((D, _), V), s), mode, Adepth) =
          collectExp (lG0, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), mode,
                      collectDec (lG0, G, (D, s), mode, Adepth))
      | collectExpW (lG0, G, (I.Lam (D, U), s), mode, Adepth) =
          collectExp (lG0, I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), mode,
                      collectDec (lG0, G, (D, s), mode, Adepth))
      | collectExpW (lG0, G, Us as (I.Root (I.BVar (k), S), s), mode,
                     Adepth as (A, depth)) = (* s = id *)
        let
          val l = I.ctxLength G
        in
          if (k = l + depth - lG0) andalso depth > 0
            then
              let
                val I.Dec (_, V) = I.ctxDec (G, k)
              (* invariant: all variables (EV or BV) in V already seen! *)
              in
                collectSpine (lG0, G, (S, s), mode, (I.Decl (A, BV), depth-1))
              end
          else
            collectSpine (lG0, G, (S, s), mode, Adepth)
        end
      | collectExpW (lG0, G, (I.Root (C, S), s), mode, Adepth) =
          collectSpine (lG0, G, (S, s), mode, Adepth)
      | collectExpW (lG0, G, (I.EVar (r, GX, V, cnstrs), s), mode,
                     Adepth as (A, depth)) =
        (case atxLookup (A, r)
           of NONE =>
              let
                val _ = checkEmpty (!cnstrs)

                val lGp' = I.ctxLength GX - lG0 + depth   (* lGp' >= 0 *)
                val w = weaken (lGp', GX, I.targetFam V)
                val iw = Whnf.invert w
                val GX' = Whnf.strengthen (iw, GX)
                val lGp'' = I.ctxLength GX' - lG0 + depth   (* lGp'' >= 0 *)
                val Vraised = raiseType (lGp'', GX', I.EClo (V, iw))
                val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw))
                val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil)
              (* invariant: all variables (EV) in Vraised already seen *)
              in
                collectSub (lG0, G, lGp'', s, mode,
                            (I.Decl (A, EV (r', Vraised, mode)), depth))
              end
            | SOME (EV (_, V, _)) =>
              let
                val lGp' = countPi V
              in
                collectSub (lG0, G, lGp', s, mode, Adepth)
              end)
       | collectExpW (lGO, G, (I.FgnExp csfe, s), mode, Adepth) =
         I.FgnExpStd.fold csfe (fn (U,Adepth') => collectExp (lGO, G, (U,s), mode, Adepth')) Adepth
           (* hack - should discuss with cs    -rv *)


    (* collectSub (lG0, G, lG'', s, mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       and  G' = GO, G''
       and  |G''| = lG''
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- s   (for the first |G'| elements of s)
    *)
    and collectSub (_, _, 0, _, _, Adepth) = Adepth
      | collectSub (lG0, G, lG', I.Shift (k), mode, Adepth) =
          collectSub (lG0, G, lG', I.Dot (I.Idx (k+1), I.Shift (k+1)),
                      mode, Adepth)
          (* eta expansion *)
      | collectSub (lG0, G, lG', I.Dot (I.Idx (k), s), mode,
                    Adepth as (A, depth)) =
          (* typing invariant guarantees that (EV, BV) in k : V already
             collected !! *)
          collectSub (lG0, G, lG'-1, s, mode, Adepth)
      | collectSub (lG0, G, lG', I.Dot (I.Exp (U), s), mode, Adepth) =
          (* typing invariant guarantees that (EV, BV) in V already
             collected !! *)
          collectSub (lG0, G, lG'-1, s, mode,
                      collectExp (lG0, G, (U, I.id), mode, Adepth))


    (* collectSpine (lG0, G, (S, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- S : V > V'
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- S
    *)
    and collectSpine (lG0, G, (I.Nil, _), mode, Adepth) = Adepth
      | collectSpine (lG0, G, (I.SClo (S, s'), s), mode, Adepth) =
          collectSpine (lG0, G, (S, I.comp (s', s)), mode, Adepth)
      | collectSpine (lG0, G, (I.App (U, S), s), mode, Adepth) =
          collectSpine (lG0, G, (S, s), mode,
                        collectExp (lG0, G, (U, s), mode, Adepth))

    (* collectDec (lG0, G, (x:D, s), mode, (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- D : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- x:D[s]
    *)
    and collectDec (lG0, G, (I.Dec (x, V), s), mode, Adepth) =
      collectExp (lG0, G, (V, s), mode, Adepth)

    (* collectModeW (lG0, G, modeIn, modeRec, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L        V[s] in whnf
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all EVars/BVars marked with modeIn in V and
                recored as modeRec
    *)
    fun collectModeW (lG0, G, modeIn, modeRec, (I.Root (I.Const cid, S), s),
                      Adepth) =
          (* s = id *)
          let
            fun collectModeW' (((I.Nil, _), ModeSyn.Mnil), Adepth) = Adepth
              | collectModeW' (((I.SClo(S, s'), s), M), Adepth) =
                  collectModeW' (((S, I.comp (s', s)), M), Adepth)
              | collectModeW' (((I.App (U, S), s), ModeSyn.Mapp (m, mS)),
                               Adepth) =
                  collectModeW' (((S, s), mS),
                                 if modeEq (m, modeIn) then
                                   collectExp (lG0, G, (U, s), modeRec, Adepth)
                                 else Adepth)
            val mS = valOf (ModeTable.modeLookup (cid))
          in
            collectModeW' (((S, s), mS), Adepth)
          end
      | collectModeW (lG0, G, modeIn, modeRec, (I.Pi ((D, P), V), s), Adepth) =
          raise Error ("Implementation restricted to the Horn fragment of the meta logic")


    (* collectG (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    fun collectG (lG0, G, Vs, Adepth) = collectGW (lG0, G, Whnf.whnf Vs, Adepth)

    and collectGW (lG0, G, Vs, Adepth) =
      collectModeW (lG0, G, M.Bot, M.Top, Vs,
                    collectModeW (lG0, G, M.Top, M.Bot, Vs, Adepth))


    (* collectDTop (lG0, G, (V, s) (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    (A'' is in mode dependecy order)
    *)
    fun collectDTop (lG0, G, Vs, Adepth) =
          collectDTopW (lG0, G, Whnf.whnf Vs, Adepth)

    and collectDTopW (lG0, G, (I.Pi ((D as I.Dec (x, V1), I.No), V2), s),
                      Adepth) =
          (* only arrows *)
          collectG (lG0, G, (V1, s),
                    collectDTop (lG0, I.Decl (G, I.decSub (D, s)),
                                 (V2, I.dot1 s), Adepth))
      | collectDTopW (lG0, G, Vs as (I.Root _, s), Adepth) =   (* s = id *)
          collectModeW (lG0, G, M.Top, M.Top, Vs, Adepth)


    (* collectDBot (lG0, G, (V, s), (A, depth)) = (A', depth')
       collects EVar's and BVar's in mode dependency order!
       depth is needed to decide if a BVar is encountered for the first time.

       Invariant:
       Let A : auxiliary context,
           depth : length of the subcontext of G, which must still
                   be traversed and collected

       If   G  |- s : G'  and   G' |- V : L
       and  G = G0, G0', GO'', Gp
       and  . |- A Atx
       and  |G0,  G0', G0''| =  lG0
       and       |G0', G0''| = depth
       then           |G0''| = depth'
       and  . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)


    fun collectDBot (lG0, G, Vs, Adepth) =
          collectDBotW (lG0, G, Whnf.whnf Vs, Adepth)
    and collectDBotW (lG0, G, (I.Pi ((D, _), V), s), Adepth) =
          collectDBot (lG0, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), Adepth)
      | collectDBotW (lG0, G, Vs as (I.Root _, s), Adepth) =  (* s = id *)
          collectModeW (lG0, G, M.Bot, M.Bot, Vs, Adepth)

    (* collect ((G,_,_), V) = A'
       collects EVar's and BVar's in V mode dependency order.

       Invariant:
       If   G  |- s : G'  and   G' |- V : L
       then . |- A' Atx
       and  A' = A, A''
       and  A'' ||- V
       and  A'' consists of all Top EVars/BVars in the head of V
                    followed by Bot/Top EVars/BVars of recursive calls
                    followed by Top EVars/BVars in the head of V
                    (A'' is in mode dependecy order)
    *)
    fun collect (M.Prefix (G, M, B), V) =
      let
        val lG0 = I.ctxLength G

        val (A, k) = collectDBot (lG0, G, (V, I.id),
                                  (collectDTop (lG0, G, (V, I.id), (I.Null, lG0))))
      in
        A
      end

    (*------------------------------------------------------------*)
    (* Second section: Abstracting over EVars and BVars that have *)
    (* been collected in mode dependency order                    *)
    (*------------------------------------------------------------*)

    (* lookupEV (A, r) = (k', V')

       Invariant:

       If   A ||- V
       and  G |- X : V' occuring in V
       then G x A |- k : V'
       and  . |- V' : type
    *)
    fun lookupEV (A, r) =
      let
        fun lookupEV' (I.Decl (A, EV (r, V, _)), r', k) =
            if (r = r') then (k, V)
            else lookupEV' (A, r', k+1)
          | lookupEV' (I.Decl (A, BV), r', k) =
              lookupEV' (A, r', k+1)
        (* lookupEV' I.Null cannot occur by invariant *)
      in
        lookupEV' (A, r, 1)
      end

    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
    fun lookupBV (A, i) =
      let
        fun lookupBV' (I.Decl (A, EV (r, V, _)), i, k) =
              lookupBV' (A, i, k+1)
          | lookupBV' (I.Decl (A, BV), 1, k) = k
          | lookupBV' (I.Decl (A, BV), i, k) =
              lookupBV' (A, i-1, k+1)
        (* lookupBV' I.Null cannot occur by invariant *)
      in
        lookupBV' (A, i, 1)
      end

    (* abstractExpW (A, G, depth, (U, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- U : V    (U,s) in whnf
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  A ||- V
       then  G0 x A, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    fun abstractExpW (A, G, depth, (V as I.Uni (L), s)) = V
      | abstractExpW (A, G, depth, (I.Pi ((D, P), V), s)) =
          Abstract.piDepend ((abstractDec (A, G, depth, (D, s)), P),
                             abstractExp (A, I.Decl (G, I.decSub (D, s)),
                                          depth + 1, (V, I.dot1 s)))
      | abstractExpW (A, G, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (A, G, depth, (D, s)),
                 abstractExp (A, I.Decl (G, I.decSub (D, s)),
                              depth + 1, (U, I.dot1 s)))
      | abstractExpW (A, G, depth, (I.Root (C as I.BVar k, S), s)) = (* s = id *)
          if k > depth then
            let
              val k' = lookupBV (A, k-depth)
            in
              I.Root (I.BVar (k'+depth), abstractSpine (A, G, depth, (S, s)))
            end
          else
            I.Root (C, abstractSpine (A, G, depth, (S, s)))
      | abstractExpW (A, G, depth, (I.Root (C, S), s)) =  (* s = id *)
          I.Root (C, abstractSpine (A, G, depth, (S, s)))
      | abstractExpW (A, G, depth, (I.EVar (r, _, V, _), s)) =
          let
            val (k, Vraised) = lookupEV (A, r)
            (* IMPROVE: remove the raised variable, replace by V -cs ?-fp *)
          in
            I.Root (I.BVar (k+depth),
                    abstractSub (A, G, depth, (Vraised, I.id),
                                 s, I.targetFam V, I.Nil))
          end
      | abstractExpW (A, G, depth, (I.FgnExp csfe, s)) =
          I.FgnExpStd.Map.apply csfe (fn U => abstractExp (A, G, depth, (U, s)))
        (* hack - should discuss with cs     -rv *)

    (* abstractExp, same as abstractExpW, but (V, s) need not be in whnf *)
    and abstractExp (A, G, depth, Us) =
          abstractExpW (A, G, depth, Whnf.whnf Us)

    (* abstractSpine (A, G, depth, (S, s)) = U'

       Invariant:
       If    G0, G |- s : G1   G1 |- S : V1 > V2
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- U  and  H ||- V1
       then  G0 x A, G |- S' : V1' > V2'
       and   . ||- S' and . ||- V1'
    *)
    and abstractSpine (A, G, depth, (I.Nil, _)) = I.Nil
      | abstractSpine (A, G, depth, (I.App (U, S), s)) =
          I.App (abstractExp (A, G, depth, (U, s)),
                 abstractSpine (A, G, depth, (S, s)))
      | abstractSpine (A, G, depth, (I.SClo (S, s'), s)) =
          abstractSpine (A, G, depth, (S, I.comp (s', s)))

    (* abstractSub (A, G, depth, (XV, t), s, b, S) = S'

       Invariant:
       If    G0, G |- s : G'
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- s
       then  G0 x A, G |- S' : {XV [t]}.W > W
       and   . ||- S'
    *)
    (* optimize: whnf not necessary *)
    and abstractSub (A, G, depth, XVt, s, b, S) =
          abstractSubW (A, G, depth, Whnf.whnf XVt, s, b, S)
    and abstractSubW (A, G, depth, (I.Root _, _), s, b, S) = S
      | abstractSubW (A, G, depth, XVt as (I.Pi _, _), I.Shift k, b, S) =
          abstractSub (A, G, depth, XVt, I.Dot (I.Idx (k+1), I.Shift (k+1)), b, S)
      | abstractSubW (A, G, depth, XVt as (I.Pi (_, XV'), t),
                      I.Dot (I.Idx (k), s), b, S) =
        let
          val I.Dec(x, V) = I.ctxDec (G, k)
        in
          if k > depth then
            let
              val k' = lookupBV (A, k-depth)
            in
              abstractSub (A, G, depth, (XV', I.dot1 t), s, b,
                           I.App (I.Root (I.BVar (k'+depth), I.Nil), S))
            end
          else
            abstractSub (A, G, depth, (XV', I.dot1 t), s, b,
                         I.App (I.Root (I.BVar (k), I.Nil), S))
        end
      | abstractSubW (A, G, depth, XVt as (I.Pi (_, XV'), t),
                      I.Dot (I.Exp (U), s), b, S) =
          abstractSub (A, G, depth, (XV', I.dot1 t), s, b,
                       I.App (abstractExp (A, G, depth, (U, I.id)), S))

    (* abstractDec (A, G, depth, (x:V, s)) = x:V'

       Invariant:
       If    G0, G |- s : G1   G1 |- V : L
       and   |G| = G
       and   |G| = depth
       and   A is auxiliary context in mode dependency order
       and   A ||- V
       then  G0 x A, G |- V' : L
       and   . ||- V'
    *)
    and abstractDec (A, G, depth, (I.Dec (xOpt, V), s)) =
          I.Dec (xOpt, abstractExp (A, G, depth, (V, s)))


    (* abstractCtx (A, (G, M)) = ((G', M') , G'')

       Let E be a list of EVars possibly occuring in G

       Invariant:
       G' = G x A
       M' = M x A    (similar to G x A, but just represents mode information)
       G'' = G [x] A
    *)
    fun abstractCtx (I.Null, GM as M.Prefix (I.Null, I.Null, I.Null)) = (GM, I.Null)
      | abstractCtx (I.Decl (A, BV), M.Prefix (I.Decl (G, D), I.Decl (M, marg), I.Decl (B, b))) =
          let
            val (M.Prefix (G', M', B'), lG') = abstractCtx (A, M.Prefix (G, M, B))
            val D' = abstractDec (A, G, 0, (D, I.id))

            val I.Dec (_, V) = D'
            val _ = if (!Global.doubleCheck) then typecheck (M.Prefix (G', M', B'), V) else ()

          in (M.Prefix (I.Decl (G', Names.decName (G', D')),
                        I.Decl (M', marg),
                        I.Decl (B', b)),
              I.Decl (lG', D'))
          end
      | abstractCtx (I.Decl (A, EV (r, V, m)), GM) =
          let
            val (M.Prefix (G', M', B'), lG') = abstractCtx (A, GM)
            val V'' = abstractExp (A, lG', 0, (V, I.id))
            val _ = if (!Global.doubleCheck) then typecheck (M.Prefix (G', M', B'), V'')
                    else ()

          in (M.Prefix (I.Decl (G', Names.decName (G', I.Dec (NONE, V''))),
                        I.Decl (M', m),
                        I.Decl (B', case m of M.Top => !MetaGlobal.maxSplit | M.Bot => 0)),
              lG')
          end

    (* abstract ((G, M), V) = ((G', M') , V')

       Invariant:
       If    G |- V : type    (M modes associated with G)
       then  G' |- V' : type  (M' modes associated with G')
       and   . ||- V'
    *)
    fun abstract (S as M.State (name, GM as M.Prefix (G, M, B), V)) =
        let
          val _ = Names.varReset I.Null
          val A = collect (GM, V)
          val (GM', _) = abstractCtx (A, GM)
          val V' = abstractExp (A, G, 0, (V, I.id))
          val S = M.State (name, GM', V')
          val _ = if (!Global.doubleCheck) then typecheck (GM', V') else ()
        in
          S
        end

  in
    val abstract = abstract
  end (* local *)
end; (* functor MetaAbstract *)
