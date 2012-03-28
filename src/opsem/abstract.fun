(* Abstraction *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga, Brigitte Pientka *)

functor AbstractTabled ((*! structure IntSyn' : INTSYN !*)
                  structure Whnf    : WHNF
                  (*! sharing Whnf.IntSyn = IntSyn' !*)
                  structure Unify   : UNIFY
                  (*! sharing Unify.IntSyn = IntSyn' !*)
                  structure Constraints : CONSTRAINTS
                  (*! sharing Constraints.IntSyn = IntSyn' !*)
                  structure Subordinate : SUBORDINATE
                  (*! sharing Subordinate.IntSyn = IntSyn' !*)
                  structure Print : PRINT
                  (*! sharing Print.IntSyn = IntSyn' !*)
                  structure Conv    : CONV
                  (*! sharing Conv.IntSyn = IntSyn' !*)
                  (*! structure TableParam : TABLEPARAM !*)
                  (*! sharing TableParam.IntSyn = IntSyn' !*)
                      )
  : ABSTRACTTABLED =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure TableParam = TableParam !*)

  exception Error of string

  local
    structure I = IntSyn
    structure C = CompSyn

    datatype Duplicates = AV of (I.Exp * int) | FGN of int

    datatype seenIn = TypeLabel | Body

    datatype ExistVars = EV of I.Exp

    fun lengthSub (I.Shift n) = 0
      | lengthSub (I.Dot(E, s)) = 1 + lengthSub s

    (*
       We write {{K}} for the context of K, where EVars have
       been translated to declarations and their occurrences to BVars.
       For each occurrence of EVar in U, we generate a distinct BVar together with
       a residual constraint. This enforces that the final abstraction of U is
       linear. However, we do not linearize the context G.

       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars in U are collected in K.
       In particular, . ||- U means U contains no EVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    fun compose'(IntSyn.Null, G) = G
      | compose'(IntSyn.Decl(G', D), G) = IntSyn.Decl(compose'(G', G), D)

    fun isId (I.Shift(n)) = (n = 0)
      | isId (s as I.Dot(I.Idx n, s')) = isId' (s, 0)
      | isId (s as I.Dot(I.Undef, s')) = isId' (s, 0)
      | isId (I.Dot(I.Exp _ , s)) = false

    and isId' (I.Shift(n), k) = (n = k)
      | isId' (I.Dot(I.Idx(i), s), k) =
      let
        val k' = k+1
      in
        (i = k') andalso isId' (s, k')
      end
      | isId' (I.Dot(I.Undef, s), k) = isId' (s, k+1)

    fun equalCtx (I.Null, s, I.Null, s') = true
      | equalCtx (I.Decl(G, D), s, I.Decl(G', D'), s') =
      Conv.convDec((D, s), (D', s')) andalso (equalCtx (G, I.dot1 s, G', I.dot1 s'))
      | equalCtx (I.Decl(G, D), s, I.Null, s') = false
      | equalCtx (I.Null, s, I.Decl(G', D'), s') = false


    (* eqEVar X Y = B
     where B iff X and Y represent same variable
     *)
    fun eqEVarW (I.EVar (r1, _, _, _)) (EV (I.EVar (r2, _, _, _))) = (r1 = r2)
      | eqEVarW _ _ = false

    fun eqEVar X1 (EV (X2)) =
      (* Sun Dec  1 14:04:17 2002 -bp  may raise exception
       if strengthening is applied,i.e. the substitution is not always id! *)
      let
        val (X1', s) = Whnf.whnf (X1, I.id)
        val (X2', s) = Whnf.whnf (X2, I.id)
      in
        eqEVarW X1' (EV (X2'))
      end

    (* a few helper functions to manage K *)
    (* member P K = B option *)
    fun member' P K =
        let fun exists' (I.Null) = NONE
              | exists' (I.Decl(K',(l, EV(Y)))) = if P(EV(Y)) then SOME(l) else exists' (K')
        in
          exists' K
        end

    (* member P K = B option *)
    fun member P K =
        let fun exists' (I.Null) = NONE
              | exists' (I.Decl(K',(i, Y))) = if P(Y) then SOME(i) else exists' (K')
        in
          exists' K
        end
    fun update' P K =
      let
        fun update' (I.Null) = I.Null
          | update' (I.Decl(K',((label, Y)))) =
          if (P Y) then
            I.Decl(K', (Body, Y))
          else I.Decl(update' (K'), (label, Y))
      in
        update' K
      end

    (* member P K = B option *)
    fun update P K =
      let
        fun update' (I.Null) = I.Null
          | update' (I.Decl(K',((label, i), Y))) =
          if (P Y) then
            I.Decl(K', ((Body, i), Y))
          else I.Decl(update' (K'), ((label, i), Y))
      in
        update' K
      end

    fun or (I.Maybe, _) = I.Maybe
      | or (_, I.Maybe) = I.Maybe
      | or (I.Meta, _) = I.Meta
      | or (_, I.Meta) = I.Meta
      | or (I.No, I.No) = I.No


    (* occursInExp (k, U) = DP,

       Invariant:
       If    U in nf
       then  DP = No      iff k does not occur in U
             DP = Maybe   iff k occurs in U some place not as an argument to a Skonst
             DP = Meta    iff k occurs in U and only as arguments to Skonsts
    *)
    fun occursInExp (k, I.Uni _) = I.No
      | occursInExp (k, I.Pi (DP, V)) = or (occursInDecP (k, DP), occursInExp (k+1, V))
      | occursInExp (k, I.Root (H, S)) = occursInHead (k, H, occursInSpine (k, S))
      | occursInExp (k, I.Lam (D, V)) = or (occursInDec (k, D), occursInExp (k+1, V))
      | occursInExp (k, I.FgnExp csfe) =
        I.FgnExpStd.fold csfe (fn (U, DP) => or (DP, (occursInExp (k, Whnf.normalize (U, I.id))))) I.No
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) =
        if (k = k') then I.Maybe
        else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
      | occursInHead (k, I.FgnConst _, DP) = DP
      | occursInHead (k, I.Skonst _, I.No) = I.No
      | occursInHead (k, I.Skonst _, I.Meta) = I.Meta
      | occursInHead (k, I.Skonst _, I.Maybe) = I.Meta
      (* no case for FVar *)

    and occursInSpine (_, I.Nil) = I.No
      | occursInSpine (k, I.App (U, S)) = or (occursInExp (k, U), occursInSpine (k, S))
      (* no case for SClo *)

    and occursInDec (k, I.Dec (_, V)) = occursInExp (k, V)
    and occursInDecP (k, (D, _)) = occursInDec (k, D)

    (* piDepend ((D,P), V) = Pi ((D,P'), V)
       where P' = Maybe if D occurs in V, P' = No otherwise
    *)
    (* optimize to have fewer traversals? -cs *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:17:10 1998 *)
    fun piDepend (DPV as ((D, I.No), V)) = I.Pi DPV
      | piDepend (DPV as ((D, I.Meta), V)) = I.Pi DPV
      | piDepend ((D, I.Maybe), V) =
          I.Pi ((D, occursInExp (1, V)), V)

    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))

    fun reverseCtx (I.Null, G) = G
      | reverseCtx (I.Decl(G, D), G') = reverseCtx(G, I.Decl(G', D))


    fun ctxToEVarSub (IntSyn.Null, s) = s
      | ctxToEVarSub (IntSyn.Decl(G,IntSyn.Dec(_,A)), s) =
      let
        val s' = ctxToEVarSub (G, s)
        val X = IntSyn.newEVar (IntSyn.Null, I.EClo(A,s'))
      in
        IntSyn.Dot(IntSyn.Exp(X), s')
      end


    (* collectExpW ((Gs, ss), Gl, (U, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- U : V      (U,s) in whnf
                Gs |- ss : G  (Gs is the strengthened context and ss is the strengthening substitution)

       No circularities in U
             (enforced by extended occurs-check for FVars in Unify)
       and   K' = K, K''
             where K' contains all EVars in (U,s)
       and  DupVars' = DupVars, DupVars''
            where DupVars' contains all duplicates in (U,s)

      if flag = true
        then duplicates of EVars are collected in DupVars
        otherwise no duplicates are collected

      note : 1) we only need to collect duplicate occurrences of EVars
                if we need to linearize the term the EVars occur in.

             2) we do not linearize fgnExp
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (Gss, Gl, (I.Uni L, s), K, DupVars, flag, d) = (K, DupVars)
      | collectExpW (Gss, Gl, (I.Pi ((D, _), V), s), K, DupVars, flag, d) =
        let
          val (K',_) = collectDec (Gss, (D, s), (K, DupVars), d, false)
        in
          (* should we apply I.dot1(ss) ? Tue Oct 15 21:55:16 2002 -bp *)
          collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (V, I.dot1 s), K', DupVars, flag, d)
        end
      | collectExpW (Gss, Gl, (I.Root (_ , S), s), K, DupVars, flag, d) =
          collectSpine (Gss, Gl, (S, s), K, DupVars, flag, d)

      | collectExpW (Gss, Gl, (I.Lam (D, U), s), K, DupVars, flag, d) =
          let
            val (K',_) = collectDec (Gss, (D, s), (K, DupVars), d, false)
          in
            collectExp (Gss, I.Decl (Gl, I.decSub (D, s)), (U, I.dot1 s), K', DupVars, flag, d+1)
          end
      | collectExpW (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
          collectEVar (Gss, Gl, (X, s), K, DupVars, flag, d)

      | collectExpW (Gss, Gl, (I.FgnExp csfe, s), K, DupVars, flag, d) =
        I.FgnExpStd.fold csfe
        (fn (U, KD') =>
         let
           val (K', Dup) = KD'
         in collectExp (Gss, Gl, (U, s), K', Dup, false, d)
         end) (K, I.Decl(DupVars, FGN(d)))

      (* No other cases can occur due to whnf invariant *)


    (* collectExp (Gss, G, Gl, (U, s), K) = K'
       same as collectExpW  but  (U,s) need not to be in whnf
    *)
    and collectExp (Gss, Gl, Us, K, DupVars, flag, d) =
        collectExpW (Gss, Gl, Whnf.whnf Us, K, DupVars, flag, d)

    (* collectSpine (Gss, Gl, (S, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G, Gl |- s : G1     G1 |- S : V > P
                Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (S, s)
       and DupVars'' contains all duplicates in (S, s)
     *)
    and collectSpine (Gss, Gl, (I.Nil, _), K, DupVars, flag, d) = (K, DupVars)
      | collectSpine (Gss, Gl, (I.SClo(S, s'), s), K, DupVars, flag, d) =
          collectSpine (Gss, Gl, (S, I.comp (s', s)), K, DupVars, flag, d)
      | collectSpine (Gss, Gl, (I.App (U, S), s), K, DupVars, flag, d) =
          let
            val  (K', DupVars') =  collectExp (Gss, Gl, (U, s), K, DupVars, flag, d)
          in
            collectSpine (Gss, Gl, (S, s), K', DupVars', flag, d)
          end

    and collectEVarFapStr (Gss, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K  of
          SOME(label) => (* we have seen X before *)
            (if flag
               then
                   collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   (* case label of
                     Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X,d)), flag, d)
                   | TypeLabel =>
                       let
                         val K' = update' (eqEVar X) K
                       in
                         collectSub(Gss, Gl, s, K', DupVars, flag, d)
                       end *)
             (* since X has occurred before, we do not traverse its type V' *)
             else
               collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
(*          val V' = raiseType (GX, V) (* inefficient! *)*)
            val label = if flag then Body else TypeLabel
            val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d)
          in
            collectSub(Gss, Gl, I.comp(w, s), I.Decl (K', (label, EV(X'))), DupVars', flag, d)
          end

    and collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K  of
          SOME(label) =>
            (* we have seen X before, i.e. it was already strengthened *)
            (if flag
              then
                  collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                  (* -bp this is a possible optimization for the variant case
                   case label of
                   Body => (print "Collect DupVar\n"; collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d) )
                 | TypeLabel =>
                    let
                      val _ = print "TypeLabel\n"
                      val K' = update' (eqEVar X) K
                    in
                      collectSub(Gss, Gl, s, K', DupVars, flag, d)
                    end*)
            else
              collectSub(Gss, Gl, s, K, DupVars, flag, d))

        | NONE =>
          let
            (* val V' = raiseType (GX, V) (* inefficient! *)*)
            val label = if flag then Body else TypeLabel
            val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d)
          in
            if flag
              then
                collectSub(Gss, Gl, I.comp(w, s), I.Decl(K', (label, EV(X'))), I.Decl(DupVars', AV(X', d)), flag, d)
            else
              collectSub(Gss, Gl, I.comp(w, s), I.Decl(K', (label, EV(X'))), DupVars', flag, d)
          end

    and collectEVarStr (Gss as (Gs, ss), Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
      let
        val w = Subordinate.weaken (GX, I.targetFam V)
        val iw = Whnf.invert w
        val GX' = Whnf.strengthen (iw, GX)
        val X' as I.EVar (r', _, _, _) = I.newEVar (GX', I.EClo (V, iw)) (* ? *)
        val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil)
        val V' = raiseType (GX', I.EClo (V, iw))
      in
        if isId (I.comp(w, I.comp(ss, s))) (* equalCtx (Gs, I.id, GX', s) *)
          then (* fully applied *)
            collectEVarFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
        else
          (* not fully applied *)
          collectEVarNFapStr (Gss, Gl, ((X', V'), w), (X, s), K, DupVars, flag, d)
      end

    (* X is fully applied pattern *)
    and collectEVarFap (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case (member (eqEVar X) K) of
          SOME(label) => (* we have seen X before *)
            (if flag
               then
                 collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 (*
                 case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end *)
                (* since X has occurred before, we do not traverse its type V' *)
             else
                collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
            (* val _ = checkEmpty !cnstrs *)
            val label = if flag then Body else TypeLabel
            val V' = raiseType (GX, V) (* inefficient! *)
            val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d)
          in
            collectSub(Gss, Gl, s, I.Decl (K', (label, EV(X))), DupVars', flag, d)
          end

    and collectEVarNFap (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
        case member' (eqEVar X) K of
          SOME(label) =>
            (if flag
               then
                 collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                 (* case label of
                   Body => collectSub(Gss, Gl, s, K, I.Decl(DupVars, AV(X, d)), flag, d)
                   | TypeLabel =>
                     let
                       val K' = update' (eqEVar X) K
                     in
                       collectSub(Gss, Gl, s, K', DupVars, flag, d)
                     end             *)
             else
               collectSub(Gss, Gl, s, K, DupVars, flag, d))
        | NONE =>
          let
            val label = if flag then Body else TypeLabel
            val V' = raiseType (GX, V) (* inefficient! *)
            val (K', DupVars') = collectExp ((I.Null, I.id), I.Null, (V', I.id), K, DupVars, false, d)
          in
            if flag
              then
                collectSub(Gss, Gl, s, I.Decl(K', (label, EV(X))), I.Decl(DupVars, AV(X, d)), flag, d)
            else
              collectSub(Gss, Gl, s, I.Decl(K', (label, EV(X))), DupVars, flag, d)
          end

    and collectEVar (Gss, Gl, (X as I.EVar (r, GX, V, cnstrs), s), K, DupVars, flag, d) =
      if (!TableParam.strengthen) then
        collectEVarStr (Gss, Gl, (X, s), K, DupVars, flag, d)
      else
        if isId(s) (* equalCtx (compose'(Gl, G), s, GX, s)  *)
          then (* X is fully applied *)
            collectEVarFap (Gss, Gl, (X, s), K, DupVars, flag, d)
        else
          (* X is not fully applied *)
          collectEVarNFap (Gss, Gl, (X, s), K, DupVars, flag, d)

    (* collectDec (Gss, G, (x:V, s), K, DupVars, flag) = (K', DupVars')

       Invariant:
       If    G |- s : G1     G1 |- V : L
            Gs |- ss : G
       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in (V, s)
       and DupVars'' contains all duplicates in (S, s)
    *)
    and collectDec (Gss, (I.Dec (_, V), s), (K, DupVars), d, flag) =
      let
(*      val (K',DupVars') =  collectExp (Gss, I.Null, (V, s), K, I.Null, false, d)*)
        val (K', DupVars') =  collectExp (Gss, I.Null, (V, s), K, DupVars, flag, d)
      in
        (K', DupVars')
      end


    (* collectSub (G, s, K, DupVars, flag) = (K', DupVars)

       Invariant:
       If    G |- s : G1

       then  K' = K, K'' and DupVars' = DupVars, DupVars''
       where K'' contains all EVars in s
       and DupVars'' contains all duplicates in s
    *)

    and collectSub (Gss, Gl, I.Shift _, K, DupVars, flag, d) = (K, DupVars)
      | collectSub (Gss, Gl, I.Dot (I.Idx _, s), K, DupVars, flag, d) =
        collectSub (Gss, Gl, s, K, DupVars, flag, d)
      | collectSub (Gss, Gl, I.Dot (I.Exp (X as I.EVar (ref (SOME U), _, _, _)), s), K, DupVars, flag, d) =
        let
          val U' = Whnf.normalize (U, I.id) (* inefficient? *)
          val (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end

      | collectSub (Gss, Gl, I.Dot (I.Exp (U as I.AVar (ref (SOME U'))), s), K, DupVars, flag, d) =
        let
          val (K', DupVars') = collectExp (Gss, Gl, (U', I.id), K, DupVars, flag, d)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end

      | collectSub (Gss, Gl, I.Dot (I.Exp (I.EClo(U', s')), s), K, DupVars, flag, d) =
        let
          val U = Whnf.normalize (U',s') (* inefficient? *)
          val (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end

      | collectSub (Gss, Gl, I.Dot (I.Exp (U), s), K, DupVars, flag, d) =
        let
          val (K', DupVars') = collectExp (Gss, Gl, (U, I.id), K, DupVars, flag, d)
        in
          collectSub (Gss, Gl, s, K', DupVars', flag, d)
        end
      | collectSub (Gss, Gl, I.Dot (I.Undef, s), K, DupVars, flag, d) =
        collectSub (Gss, Gl, s, K, DupVars, flag, d)

    (* collectCtx (Gss, G0, G, K) = (K', DupVars)
       Invariant:
       If G0 |- G ctx,
       then G0' = G0,G
       and K' = K, K'' where K'' contains all EVars in G
    *)

    fun collectCtx (Gss,C.DProg(I.Null, I.Null), (K, DupVars), d) =  (K, DupVars)
      | collectCtx (Gss, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Parameter)), (K, DupVars), d) =
        let
          val (K',DupVars') = collectCtx (Gss, C.DProg(G, dPool), (K, DupVars), d - 1)
        in
          collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false)
        end
      | collectCtx (Gss, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Dec(r,s,Ha))), (K, DupVars), d) =
        let
          val (K', DupVars') = collectCtx (Gss, C.DProg(G, dPool), (K, DupVars), d - 1)
        in
          collectDec (Gss, (D, I.id), (K', DupVars'), d - 1, false)
        end


    (* abstractExpW (epos, apos, Vars, Gl, total, depth, (U, s), eqn) = (epos', apos', Vars', U', eqn')
      (abstraction and linearization of existential variables in (U,s))

       U' = {{U[s]}}_(K, Dup)

       Invariant:
       If     G, Gl |- U[s] : V and  U[s] is in whnf
       and   |Gl| = depth
             |Dup, K| = total

       and epos = (total(K) + l) - #replaced expressions in U    (generate no additional constraints)
       and apos = (total(Dup) + + total(K) + l) - #replaced expressions in U
                  (generate additional constraints (avars))

       and Vars'  = Vars, Vars''
           where Vars contains pairs ((label, i), EV X) of all EVars (EV X),
           where label refers to where we have seen the existential variable (typeLabel or body) and
           i corresponds to the bvar-index assigned to X in U[s]

       and   K ~ Vars (we can obtain K from Vars by dropping the first component of
             each pair (_, EV X) in Vars' )

       then   {{Dup}}, {{K}}  ||- U
       and {{Dup}} {{K}} , G, Gl |-  U' : V'
       and eqn' = eqn, eqn'' where eqn'' are residual equations relating between elements
           in {{K}} and {{Dup}}

       and . ||- Pi G. U'  and   U' is in nf

       if flag then linearize U else allow duplicates.

    *)

    fun abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (U as I.Uni (L), s), eqn) =
        (posEA, Vars, U, eqn)
      | abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Pi ((D, P), V), s), eqn) =
        let
          val (posEA', Vars', D, _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE)
          val (posEA'', Vars'', V', eqn2) = abstractExp (flag, Gs, posEA', Vars', Gl, total, depth + 1, (V, I.dot1 s), eqn)
        in
          (posEA'', Vars'', piDepend ((D, P), V'),eqn2)
        end
      | abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Root (H, S) ,s), eqn) =
        let
          val (posEA', Vars', S, eqn') = abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn)
        in
          (posEA', Vars', I.Root (H, S), eqn')
        end
      | abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, (I.Lam (D, U), s), eqn) =
        let
          val (posEA', Vars', D', _) = abstractDec (Gs, posEA, Vars, Gl, total, depth, (D, s), NONE)
          val (posEA'', Vars'', U', eqn2) = abstractExp (flag, Gs, posEA', Vars', I.Decl(Gl, D'), total, depth + 1, (U, I.dot1 s), eqn)
        in
          (posEA'', Vars'', I.Lam (D',U' ), eqn2)
        end
      | abstractExpW (flag, Gs as (Gss, ss), posEA as (epos, apos), Vars, Gl, total, depth, (X as I.EVar (_, GX, VX, _), s), eqn) =
        (* X is possibly strengthened ! *)
        if  isId(I.comp(ss, s))
           then  (* X is fully applied *)
             abstractEVarFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)
         else
           (* s =/= id, i.e. X is not fully applied *)
          abstractEVarNFap (flag, Gs, posEA, Vars, Gl, total, depth, (X, s), eqn)

(*      | abstractExpW (posEA, Vars, Gl, total, depth, (X as I.FgnExp (cs, ops), s), eqn) =  *)
(*      let
          val (X, _) = #map(ops) (fn U => abstractExp (posEA, Vars, Gl, total, depth, (U, s), eqn))
        in        abstractFgn (posEA, Vars, Gl, total, depth, X, eqn)
        end
*)

    (* abstractExp (posEA, Vars, Gl, total, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
    and abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, Us, eqn) =
        abstractExpW (flag, Gs, posEA, Vars, Gl, total, depth, Whnf.whnf Us, eqn)

    and abstractEVarFap (flag, Gs, posEA as (epos, apos), Vars, Gl, total, depth, (X, s), eqn) =
      case (member (eqEVar X) Vars) of
        SOME(label, i) =>  (* we have seen X before *)
          if flag then
            (* enforce linearization *)
            case label of
              Body =>
                let
                  val BV = I.BVar(apos + depth)
                  val BV' = I.BVar(i + depth)
                  val BV1 = I.BVar(apos + depth)
                  val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                in
                  (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
                end
            | TypeLabel =>
                let
                  val Vars' = update (eqEVar X) Vars
                  val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                in
                  (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                end

          else  (* do not enforce linearization -- used for type labels *)
            let
              val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn)
            in
              (posEA', Vars', I.Root(I.BVar(i + depth), S), eqn1)
            end
         | NONE => (* we see X for the first time *)
            let
              val label = if flag then Body else TypeLabel
              val BV = I.BVar(epos + depth)
              val pos = (epos - 1, apos)
              val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, pos, I.Decl(Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn)
            in
              (posEA', Vars', I.Root(BV, S), eqn1)
            end

    and abstractEVarNFap (flag, Gs, posEA as (epos, apos), Vars, Gl, total, depth, (X, s), eqn) =
      case (member (eqEVar X) Vars) of
        SOME(label, i) =>  (* we have seen X before *)
          if flag then
            (* enforce linearization *)
            let
              val BV = I.BVar(apos + depth)
              val BV' = I.BVar(i + depth)
              val BV1 = I.BVar(apos + depth)
              val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
            in
              (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
            end
            (* (case label of
               Body =>
                 let
                  val _ = print "abstractEVarNFap -- flag true; we have seen X before\n"
                   val BV = I.BVar(apos + depth)
                   val BV' = I.BVar(i + depth)
                   val BV1 = I.BVar(apos + depth)
                   val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos - 1), Vars, Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil ), eqn1))
                 end
              | TyeLabel =>
                 let
                   val Vars' = update (eqEVar X) Vars
                   val (posEA', Vars'', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars', Gl, total, depth, s, I.Nil, eqn)
                 in
                   (posEA', Vars'', I.Root(I.BVar(i + depth), S), eqn1)
                 end) *)
          else (* do not enforce linearization -- used for type labels *)
            let
              val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos, apos), Vars, Gl, total, depth, s, I.Nil, eqn)
            in
              (posEA', Vars', I.Root(I.BVar(i + depth), S), eqn1)
            end
         | NONE => (* we have not seen X before *)
           if flag then
             (* enforce linearization since X is not fully applied *)
             let
               val label = if flag then Body else TypeLabel
               val BV = I.BVar(apos + depth)
               val BV' = I.BVar(epos + depth)
               val BV1 = I.BVar(apos + depth)
               val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos - 1),  I.Decl(Vars, ((label, epos), EV X)), Gl, total, depth, s, I.Nil, eqn)
             in
               (posEA', Vars', I.Root(BV, I.Nil), TableParam.Unify(Gl, I.Root(BV', S), I.Root(BV1, I.Nil), eqn1))
             end
           else (* do not enforce linearization -- used for type labels *)
             let
               val (posEA', Vars', S, eqn1) = abstractSub (flag, Gs, (epos - 1, apos),  I.Decl(Vars, ((TypeLabel, epos), EV X)), Gl, total, depth, s, I.Nil, eqn)
             in
               (posEA', Vars', I.Root(I.BVar(epos+depth), S), eqn1)
             end


    (* abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, S, eqn) = (posEA', Vars', S', eqn')

       (implicit raising)
       (for posEA, Vars, eqn explanation see above)

       let K* = K, Dup

       S' = {{s}}_K* @@ S

       Invariant:
       If    G, Gl |- s : G1
       and  |Gl| = depth

       and   {{Dup}} {{K}} ||- s
       then {{Dup}} {{K}}, G, Gl |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Shift (k), S, eqn) =
        if k < depth
          then abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S, eqn)
        else (* k = depth *) (posEA, Vars, S, eqn)
      | abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Idx (k), s), S, eqn) =
          abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, s, I.App (I.Root (I.BVar (k), I.Nil), S), eqn)
      | abstractSub (flag, Gs, posEA, Vars, Gl, total, depth, I.Dot (I.Exp (U), s), S, eqn) =
          let
            val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U, I.id), eqn)
          in
            abstractSub (flag, Gs, posEA', Vars', Gl, total, depth, s, I.App (U', S), eqn')
          end


    (* abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, s), eqn) = (posEA', Vars', S', eqn')
       where S' = {{S[s]}}_K*   and K* = K, Dup

       Invariant:
       If   Gl, G |- s : G1     G1 |- S : V > P
       and  K* ||- S
       and  |G| = depth

       then {{K*}}, G, G |- S' : V' > P'
       and  . ||- S'
    *)

    and abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.Nil, _), eqn)  =
        (posEA, Vars, I.Nil, eqn)
      | abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.SClo (S, s'), s), eqn) =
          abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (S, I.comp (s', s)), eqn)
      | abstractSpine (flag, Gs, posEA, Vars, Gl, total, depth, (I.App (U, S), s), eqn) =
          let
            val (posEA', Vars', U', eqn') = abstractExp (flag, Gs, posEA, Vars, Gl, total, depth, (U ,s), eqn)
            val (posEA'', Vars'', S', eqn'') = abstractSpine (flag, Gs, posEA', Vars', Gl, total, depth, (S, s), eqn')
          in
            (posEA'', Vars'', I.App (U', S'), eqn'')
          end


    (* abstractSub' (flag, Gs, epos, K, Gl, total, s) = (epos', K', s')      (implicit raising)

        Invariant:
        If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       and {{K}}, G |- {{s}}_K : G1
       then Gs, G |- s' : G1    where  s' == {{s}}_K

         *)

    and abstractSub' (flag, Gs, epos, Vars, total, I.Shift (k)) =
        if k < 0
          then
            raise Error ("Substitution out of range\n")
        else
          (epos, Vars, I.Shift(k + total))
      | abstractSub' (flag, Gs, epos, Vars, total, I.Dot (I.Idx (k), s)) =
          let
            val (epos', Vars', s') = abstractSub' (flag, Gs, epos, Vars, total, s)
          in
            (epos', Vars', I.Dot(I.Idx(k),s'))
          end
      | abstractSub' (flag, Gs, epos, Vars, total, I.Dot (I.Exp (U), s)) =
          let
            val ((ep, _), Vars', U', _) = abstractExp (false, Gs, (epos, 0), Vars, I.Null, total, 0, (U, I.id), TableParam.Trivial)
            val (epos'', Vars'', s') = abstractSub' (flag, Gs, ep, Vars', total, s)
          in
            (epos'', Vars'', I.Dot(I.Exp(U'), s'))
          end


    (* abstractDec (Gs, posEA, Vars, Gl, total, depth, (x:V, s)) = (posEA', Vars', x:V')
       where V = {{V[s]}}_K*

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K* ||- V
       and  |G| = depth

       then {{K*}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), NONE) =
      let
(*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)

        val (posEA', Vars', V',eqn) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)
      in
        (posEA', Vars', I.Dec (x, V'), eqn)
      end

      | abstractDec (Gs, posEA, Vars, Gl, total, depth, (I.Dec (x, V), s), SOME(eqn)) =
      let
(*      val (posEA', Vars', V', _) = abstractExp (false, Gs, posEA, Vars, Gl, total, depth, (V, s), TableParam.Trivial)*)

        val (posEA', Vars', V',eqn') = abstractExp (true, Gs, posEA, Vars, Gl, total, depth, (V, s), eqn)
      in
        (posEA', Vars', I.Dec (x, V'), eqn')
      end


    (* abstractCtx (Gs, epos, K, total, depth, C.DProg(G,dPool)) = (epos', K', G')
       where G' = {{G}}_K

       Invariants:
       If K ||- G
       and |G| = depth
       then {{K}} |- G' ctx
       and . ||- G'
       and epos = current epos

       note: we will linearize all dynamic assumptions in G.
    *)
    fun abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Null, I.Null), G', eqn) =
        (epos, Vars, G', eqn)
      | abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Decl (G, D), I.Decl(dPool, C.Parameter)), G', eqn) =
        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), NONE)
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn)
        end
      | abstractCtx' (Gs, epos, Vars, total, depth, C.DProg(I.Decl (G, D), I.Decl(dPool, _)), G', eqn) =
      let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', _) = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), NONE)
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn)
        end
(*        let
          val d = IntSyn.ctxLength (G)
          val ((epos', _), Vars', D', eqn') = abstractDec (Gs, (epos, total), Vars, I.Null, total , depth - 1, (D, I.id), SOME(eqn))
        in
          abstractCtx' (Gs, epos', Vars', total, depth - 1, C.DProg(G, dPool), I.Decl (G', D'), eqn')
        end
*)
    fun abstractCtx (Gs, epos, Vars, total, depth, dProg) =
      abstractCtx' (Gs, epos, Vars, total, depth, dProg, I.Null, TableParam.Trivial)


    (* makeEVarCtx (Gs, Kall, D, K, eqn) = G'  *)
    fun makeEVarCtx (Gs, Vars, DEVars, I.Null, total) = DEVars
      | makeEVarCtx (Gs, Vars, DEVars, I.Decl (K', (_, EV (E as I.EVar (_, GX, VX, _)))),total) =
        let
          val V' = raiseType (GX, VX)
          val ( _,Vars', V'', _) = abstractExp (false, Gs, (0, 0),  Vars, I.Null, 0,
                                                (total - 1), (V', I.id),  TableParam.Trivial)
          val  DEVars' = makeEVarCtx (Gs, Vars', DEVars, K', total - 1)
          val DEVars'' = I.Decl (DEVars', I.Dec (NONE, V''))
        in
          DEVars''
        end

    fun makeAVarCtx (Vars, DupVars) =
      let
        fun avarCtx (Vars, I.Null, k) = I.Null
          | avarCtx (Vars, I.Decl (K', AV (E as I.EVar (ref NONE, GX, VX, _), d)), k) =
          I.Decl(avarCtx (Vars, K', k+1),
                 I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d))
          | avarCtx (Vars, I.Decl (K', AV (E as I.EVar (_, GX, VX, _), d)), k) =
          I.Decl(avarCtx (Vars, K', k+1),
                 I.ADec (SOME("AVar "^Int.toString k ^ "--" ^ Int.toString d), d))
      in
        avarCtx (Vars, DupVars, 0)
      end
      (* add case for foreign expressions ? *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    fun lowerEVar' (X, G, (I.Pi ((D',_), V'), s')) =
        let
          val D'' = I.decSub (D', s')
          val (X', U) = lowerEVar' (X, I.Decl (G, D''), Whnf.whnf (V', I.dot1 s'))
        in
          (X', I.Lam (D'', U))
        end
      | lowerEVar' (X, G, Vs') =
        let
          val X' = X
        in
          (X', X')
        end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and (* lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) = *)
      lowerEVar1 (X, I.EVar (r, G, _, _), (V as I.Pi _, s)) =
        let
          val (X', U) = lowerEVar' (X, G, (V,s))
        in
          I.EVar(ref (SOME(U)), I.Null, V, ref nil)
        end
      | lowerEVar1 (_, X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and
      lowerEVar (E, X as I.EVar (r, G, V, ref nil)) = lowerEVar1 (E, X, Whnf.whnf (V, I.id))
      | lowerEVar (E, I.EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "abstraction : LowerEVars: Typing ambiguous -- constraint of functional type cannot be simplified"


    (* evarsToSub (K, s') = s
      Invariant:
      if K = EV Xn ... EV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)
    fun evarsToSub (I.Null, s) = s
      | evarsToSub (I.Decl (K', (_, EV (E as I.EVar (I as (ref NONE), GX, VX, cnstr)))),s) =
      let
        val V' = raiseType (GX, VX) (* redundant ? *)
        val X = lowerEVar1 (E, I.EVar(I, I.Null, V', cnstr), Whnf.whnf(V', I.id))
        val s' = evarsToSub (K', s)
      in
        I.Dot(I.Exp(X), s')
      end

    (* evarsToSub (K, s') = s
      Invariant:
      if K = AV Xn ... AV X2, EV X1
        then
        s = X1 . X2 . ... s'
     *)

    fun avarsToSub (I.Null, s) = s
      | avarsToSub (I.Decl (Vars', (AV (E as I.EVar (I, GX, VX, cnstr), d))), s) =
        let
          val s' = avarsToSub (Vars', s)
          val X' as I.AVar(r) = I.newAVar ()
        in
          I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s')
        end


  (* abstractEVarCtx (G, p, s) = (G', D', U', s')

     if G |- p[s] and s contains free variables X_n .... X_1
     then
       D' |- Pi  G' . U'
       where D' is the abstraction over the free vars X_n .... X_1

       and s' is a substitution the free variables
            X_n .... X_1, s.t.

       . |- s' : D'

       . |- (Pi G' .U' )[s']  is equivalent to . |- Pi G . p[s]

       Note: G' and U' are possibly strengthened
   *)

    fun abstractEVarCtx (dp as C.DProg(G,dPool), p, s) =
      let
        val (Gs, ss, d) =  (if (!TableParam.strengthen) then
                              let
                                val w' = Subordinate.weaken (G, I.targetFam p)
                                val iw = Whnf.invert w'
                                val G' = Whnf.strengthen (iw, G)
                                val d' = I.ctxLength (G')
                              in
                                (G', iw, d')
                              end
                            else
                              (G, I.id, I.ctxLength(G)))
         val (K, DupVars) = collectCtx ((Gs, ss), dp, (I.Null, I.Null), d)
         (* K ||- G i.e. K contains all EVars in G *)
         val (K', DupVars') = collectExp((Gs, ss), I.Null, (p, s), K, DupVars, true, d)
         (* DupVars' , K' ||- p[s]  i.e. K' contains all EVars in (p,s) and G and
                                         DupVars' contains all duplicate EVars p[s] *)
         val epos = I.ctxLength(K')
         val apos = I.ctxLength(DupVars')
         val total = epos + apos
         val (epos', Vars', G', eqn) = abstractCtx ((Gs,ss), epos, I.Null, total , d, dp)
         (* {{G}}_Vars' , i.e. abstract over the existential variables in G*)
         val (posEA'' (* = 0 *), Vars'', U', eqn') = abstractExp (true, (Gs, ss), (epos', total), Vars', I.Null,
                                                                  total, d, (p,s), eqn)
         (* abstract over existential variables in p[s] and linearize the expression *)
         val DAVars = makeAVarCtx (Vars'', DupVars')
         val DEVars = makeEVarCtx ((Gs, ss), Vars'', I.Null, Vars'', 0 (* depth *))
         (* note: depth will become negative during makeEVarCtx *)

         val s' = avarsToSub (DupVars', I.id)
         val s'' = evarsToSub (Vars'', s')

         val G'' = reverseCtx (G', I.Null)
       in
         if (!TableParam.strengthen) then
           let
             val w' = Subordinate.weaken (G'', I.targetFam U')
             val iw = Whnf.invert w'
             val Gs' = Whnf.strengthen (iw, G'')
           in
             (Gs', DAVars, DEVars, U', eqn', s'')
           end
         else
           (G'', DAVars, DEVars, U', eqn', s'')
       end


  in

    val abstractEVarCtx = abstractEVarCtx

  (* abstractAnswSub s = (D', s')

   if  |- s : Delta' and s may contain free variables and
     D |- Pi G. U  and  |- s : D and  |- (Pi G . U)[s]
    then

    D' |- s' : D   where D' contains all the
    free variables from s
   *)

    val abstractAnswSub =
      (fn s =>
       let
         (* no linearization for answer substitution *)
         val (K, _ ) = collectSub((I.Null, I.id), I.Null, s, I.Null, I.Null, false, 0)
         val epos = I.ctxLength K
         val (_ (*0 *), Vars, s') = abstractSub' (false, (I.Null, I.id), epos, I.Null, epos (* total *), s)

         val DEVars = makeEVarCtx ((I.Null, I.id), Vars, I.Null, Vars,  0)
         val s1' = ctxToEVarSub (DEVars, I.id)
       in
         (DEVars, s')
       end)

    val raiseType = (fn (G, U) =>
                       raiseType (G, U))

  end
end;  (* functor AbstractTabled *)



