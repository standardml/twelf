(* Meta Theorem Prover abstraction : Version 1.3 *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor MTPAbstract ((*! structure IntSyn' : INTSYN !*)
                     (*! structure FunSyn' : FUNSYN !*)
                     (*! sharing FunSyn'.IntSyn = IntSyn' !*)
                     structure StateSyn' : STATESYN
                     (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                     structure Whnf    : WHNF
                     (*! sharing Whnf.IntSyn = IntSyn' !*)
                     structure Constraints : CONSTRAINTS
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     structure Unify : UNIFY
                     (*! sharing Unify.IntSyn = IntSyn' !*)
                     structure Subordinate : SUBORDINATE
                     (*! sharing Subordinate.IntSyn = IntSyn' !*)
                     structure TypeCheck : TYPECHECK
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     structure FunTypeCheck : FUNTYPECHECK
                     (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                       sharing FunTypeCheck.StateSyn = StateSyn'
                     structure Abstract : ABSTRACT
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                       )
  : MTPABSTRACT =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  datatype ApproxFor =                  (* Approximat formula *)
    Head of IntSyn.dctx * (FunSyn.For * IntSyn.Sub) * int       (* AF ::= F [s] *)
  | Block of (IntSyn.dctx * IntSyn.Sub * int * IntSyn.Dec list) * ApproxFor
                                        (*      | (t, G2), AF *)

  local

    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn
    structure C = Constraints

    (* Intermediate Data Structure *)

    datatype EBVar =
      EV of I.Exp option ref * I.Exp * S.Tag * int
                                        (* y ::= (X , {G2} V)  if {G1, G2 |- X : V
                                          |G1| = d *)
    | BV of I.Dec * S.Tag



    (*
       We write {{K}} for the context of K, where EVars and BVars have
       been translated to declarations and their occurrences to BVars.
       We write {{U}}_K, {{S}}_K for the corresponding translation of an
       expression or spine.

       Just like contexts G, any K is implicitly assumed to be
       well-formed and in dependency order.

       We write  K ||- U  if all EVars and BVars in U are collected in K.
       In particular, . ||- U means U contains no EVars or BVars.  Similarly,
       for spines K ||- S and other syntactic categories.

       Collection and abstraction raise Error if there are unresolved
       constraints after simplification.
    *)

    (* checkEmpty Cnstr = ()
       raises Error exception if constraints Cnstr cannot be simplified
       to the empty constraint
    *)
    fun checkEmpty (nil) = ()
      | checkEmpty (cnstrL) =
        (case C.simplify cnstrL
           of nil => ()
            | _ => raise Error "Typing ambiguous -- unresolved constraints")

    (* eqEVar X Y = B
       where B iff X and Y represent same variable
    *)
    fun eqEVar (I.EVar (r1, _, _, _)) (EV (r2, _, _, _)) = (r1 = r2)
      | eqEVar _ _ = false


    (* exists P K = B
       where B iff K = K1, Y, K2  s.t. P Y  holds
    *)
    fun exists P K =
        let fun exists' (I.Null) = false
              | exists' (I.Decl(K',Y)) = P(Y) orelse exists' (K')
        in
          exists' K
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
      (* no case for Redex, EVar, EClo *)

    and occursInHead (k, I.BVar (k'), DP) =
        if (k = k') then I.Maybe
        else DP
      | occursInHead (k, I.Const _, DP) = DP
      | occursInHead (k, I.Def _, DP) = DP
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

    (* weaken (depth,  G, a) = (w')
    *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
        let
          val w' = weaken (G', a)
        in
          if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end

    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Pi ((D, I.Maybe), V))

    fun restore (0, Gp) = (Gp, I.Null)
      | restore (n, I.Decl (G, D)) =
        let
          val (Gp', GX') = restore (n - 1, G)
        in
          (Gp', I.Decl (GX', D))
        end

    fun concat (Gp, I.Null) = Gp
      | concat (Gp, I.Decl (G, D)) =
         I.Decl (concat (Gp, G), D)


    (* collectExpW (T, d, G, (U, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
             (enforced by extended occurs-check for BVars in Unify)
       and   K' = K, K''
             where K'' contains all EVars and BVars in (U,s)
    *)
    (* Possible optimization: Calculate also the normal form of the term *)
    fun collectExpW (T, d, G, (I.Uni L, s), K) = K
      | collectExpW (T, d, G, (I.Pi ((D, _), V), s), K) =
          collectExp (T, d, I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (T, d, G, (D, s), K))
      | collectExpW (T, d, G, (I.Root (_ , S), s), K) =
          collectSpine (S.decrease T, d, G, (S, s), K)
      | collectExpW (T, d, G, (I.Lam (D, U), s), K) =
          collectExp (T, d, I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (T, d, G, (D, s), K))
      | collectExpW (T, d, G, (X as I.EVar (r, GdX, V, cnstrs), s), K) =
          if exists (eqEVar X) K
            then collectSub (T, d, G, s, K)
          else let
                 val (Gp, GX) = restore (I.ctxLength GdX - d, GdX)   (* optimization possible for d = 0 *)
                 val _ = checkEmpty (!cnstrs)
                 val w = weaken (GX, I.targetFam V)
                 val iw = Whnf.invert w
                 val GX' = Whnf.strengthen (iw, GX)
                 val X' as I.EVar (r', _, _, _) = I.newEVar (concat (Gp, GX'), I.EClo (V, iw))
                 val _ = Unify.instantiateEVar (r, I.EClo (X', w), nil)
                 val V' = raiseType (GX', I.EClo (V, iw))
               in
                 collectSub (T, d, G, I.comp (w, s), I.Decl (collectExp (T, d, Gp, (V', I.id), K), EV (r', V', T, d)))
               end
      | collectExpW (T, d, G, (I.FgnExp csfe, s), K) =
        I.FgnExpStd.fold csfe (fn (U, K') => collectExp (T, d, G, (U, s), K')) K
          (* hack - should consult cs    -rv *)
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (T, d, G, (U, s), K) = K'

       same as collectExpW  but  (U,s) need not to be in whnf
    *)
    and collectExp (T, d, G, Us, K) = collectExpW (T, d, G, Whnf.whnf Us, K)

    (* collectSpine (T, d, G, (S, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and BVars in (S, s)
     *)
    and collectSpine (T, d, G, (I.Nil, _), K) = K
      | collectSpine (T, d, G, (I.SClo(S, s'), s), K) =
          collectSpine (T, d, G, (S, I.comp (s', s)), K)
      | collectSpine (T, d, G, (I.App (U, S), s), K) =
          collectSpine (T, d, G, (S, s), collectExp (T, d, G, (U, s), K))

    (* collectDec (T, d, G, (x:V, s), K) = K'

       Invariant:
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and BVars in (V, s)
    *)
    and collectDec (T, d, G, (I.Dec (_, V), s), K) =
          collectExp (T, d, G, (V, s), K)

    (* collectSub (T, d, G, s, K) = K'

       Invariant:
       If    G |- s : G1
       then  K' = K, K''
       where K'' contains all EVars and BVars in s
    *)
    and collectSub (T, d, G, I.Shift _, K) = K
      | collectSub (T, d, G, I.Dot (I.Idx _, s), K) = collectSub (T, d, G, s, K)
      | collectSub (T, d, G, I.Dot (I.Exp (U), s), K) =
          collectSub (T, d, G, s, collectExp (T, d, G, (U, I.id), K))

    (* abstractEVar (K, depth, X) = C'

       Invariant:
       If   G |- X : V
       and  |G| = depth
       and  X occurs in K  at kth position (starting at 1)
       then C' = BVar (depth + k)
       and  {{K}}, G |- C' : V
    *)
    fun abstractEVar (I.Decl (K', EV (r', _, _, d)), depth, X as I.EVar (r, _, _, _)) =
        if r = r' then (I.BVar (depth+1), d)
        else abstractEVar (K', depth+1, X)
      | abstractEVar (I.Decl (K', BV _), depth, X) =
          abstractEVar (K', depth+1, X)



    (* lookupBV (A, i) = k'

       Invariant:

       If   A ||- V
       and  G |- V type
       and  G [x] A |- i : V'
       then ex a substititution  G x A |- s : G [x] A
       and  G x A |- k' : V''
       and  G x A |- V' [s] = V'' : type
    *)
    fun lookupBV (K, i) =
      let
        fun lookupBV' (I.Decl (K, EV (r, V, _, _)), i, k) =
              lookupBV' (K, i, k+1)
          | lookupBV' (I.Decl (K, BV _), 1, k) = k
          | lookupBV' (I.Decl (K, BV _), i, k) =
              lookupBV' (K, i-1, k+1)
        (* lookupBV' I.Null cannot occur by invariant *)
      in
        lookupBV' (K, i, 1)
      end



    (* abstractExpW (K, depth, (U, s)) = U'
       U' = {{U[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)
    fun abstractExpW (K, depth, (U as I.Uni (L), s)) = U
      | abstractExpW (K, depth, (I.Pi ((D, P), V), s)) =
          piDepend ((abstractDec (K, depth, (D, s)), P),
                    abstractExp (K, depth + 1, (V, I.dot1 s)))
      | abstractExpW (K, depth, (I.Root (H as I.BVar k, S), s)) = (* s = id *)
          if k > depth then
            let
              val k' = lookupBV (K, k-depth)
            in
              I.Root (I.BVar (k'+depth), abstractSpine (K, depth, (S, s)))
            end
          else
          I.Root (H, abstractSpine (K, depth, (S, s)))
      | abstractExpW (K, depth, (I.Root (H, S) ,s)) =
          I.Root (H, abstractSpine (K, depth, (S, s)))
      | abstractExpW (K, depth, (I.Lam (D, U), s)) =
          I.Lam (abstractDec (K, depth, (D, s)),
                 abstractExp (K, depth + 1, (U, I.dot1 s)))
      | abstractExpW (K, depth, (X as I.EVar (_, G, _, _), s)) =
          let
            val (H, d) = abstractEVar (K, depth, X)
          in
            I.Root (H, abstractSub (I.ctxLength G - d,  K, depth, s, I.Nil))
          end
      | abstractExpW (K, depth, (I.FgnExp csfe, s)) =
          I.FgnExpStd.Map.apply csfe (fn U => abstractExp (K, depth, (U, s)))
          (* hack - should consult cs   -rv *)

    (* abstractExp (K, depth, (U, s)) = U'

       same as abstractExpW, but (U,s) need not to be in whnf
    *)
    and abstractExp (K, depth, Us) = abstractExpW (K, depth, Whnf.whnf Us)

    (* abstractSub (K, depth, s, S) = S'      (implicit raising)
       S' = {{s}}_K @@ S

       Invariant:
       If   G |- s : G1
       and  |G| = depth
       and  K ||- s
       then {{K}}, G |- S' : {G1}.W > W   (for some W)
       and  . ||- S'
    *)
    and abstractSub (n, K, depth, I.Shift (k), S) =
        if n > 0
          then abstractSub (n, K, depth, I.Dot (I.Idx (k+1), I.Shift (k+1)), S)
        else (* n = 0 *) S
      | abstractSub (n, K, depth, I.Dot (I.Idx (k), s), S) =
        let
          val H = if k > depth then
                    let
                      val k' = lookupBV (K, k-depth)
                    in
                      I.BVar (k'+depth)
                    end
                  else
                    I.BVar (k)
        in
          abstractSub (n-1, K, depth, s, I.App (I.Root (H, I.Nil), S))
        end
      | abstractSub (n, K, depth, I.Dot (I.Exp (U), s), S) =
          abstractSub (n-1, K, depth, s, I.App (abstractExp (K, depth, (U, I.id)), S))

    (* abstractSpine (K, depth, (S, s)) = S'
       where S' = {{S[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- S : V > P
       and  K ||- S
       and  |G| = depth

       then {{K}}, G |- S' : V' > P'
       and  . ||- S'
    *)
    and abstractSpine (K, depth, (I.Nil, _))  = I.Nil
      | abstractSpine (K, depth, (I.SClo (S, s'), s)) =
          abstractSpine (K, depth, (S, I.comp (s', s)))
      | abstractSpine (K, depth, (I.App (U, S), s)) =
          I.App (abstractExp (K, depth, (U ,s)),
                 abstractSpine (K, depth, (S, s)))

    (* abstractDec (K, depth, (x:V, s)) = x:V'
       where V = {{V[s]}}_K

       Invariant:
       If   G |- s : G1     G1 |- V : L
       and  K ||- V
       and  |G| = depth

       then {{K}}, G |- V' : L
       and  . ||- V'
    *)
    and abstractDec (K, depth, (I.Dec (x, V), s)) =
          I.Dec (x, abstractExp (K, depth, (V, s)))

    (* getlevel (V) = L if G |- V : L

       Invariant: G |- V : L' for some L'
    *)
    fun getLevel (I.Uni _) = I.Kind
      | getLevel (I.Pi (_, U)) = getLevel U
      | getLevel (I.Root _)  = I.Type
      | getLevel (I.Redex (U, _)) = getLevel U
      | getLevel (I.Lam (_, U)) = getLevel U
      | getLevel (I.EClo (U,_)) = getLevel U

    (* checkType (V) = () if G |- V : type

       Invariant: G |- V : L' for some L'
    *)
    fun checkType V =
        (case getLevel V
           of I.Type => ()
            | _ => raise Error "Typing ambiguous -- free type variable")



    (* abstractCtx (K, V) = V'
       where V' = {{K}} V

       Invariant:
       If   {{K}} |- V : L
       and  . ||- V

       then V' = {{K}} V
       and  . |- V' : L
       and  . ||- V'
    *)
    fun abstractCtx (I.Null) = (I.Null, I.Null)
      | abstractCtx (I.Decl (K', EV (_, V', T as S.Lemma (b), _))) =
        let
          val V'' = abstractExp (K', 0, (V', I.id))
          val _ = checkType V''
          val (G', B') = abstractCtx K'
          val D' = I.Dec (NONE, V'')
        in
          (I.Decl (G', D'), I.Decl (B', T))
        end
      | abstractCtx (I.Decl (K', EV (_, V', T as S.None, _))) =
        let
          val V'' = abstractExp (K', 0, (V', I.id))
          val _ = checkType V''
          val (G', B') = abstractCtx K'
          val D' = I.Dec (NONE, V'')
        in
          (I.Decl (G', D'), I.Decl (B', S.None))
        end
      | abstractCtx (I.Decl (K', BV (D, T))) =
        let
          val D' = abstractDec (K', 0, (D, I.id))
          val (G', B') = abstractCtx K'
        in
          (I.Decl (G', D'), I.Decl (B', T))
        end



    (* abstractGlobalSub (K, s, B) = s'

       Invariant:
       If   K > G   aux context
       and  G |- s : G'
       then K |- s' : G'
    *)


    fun abstractGlobalSub (K, I.Shift _, I.Null) = I.Shift (I.ctxLength K)
      | abstractGlobalSub (K, I.Shift n, B as I.Decl _) =
          abstractGlobalSub (K, I.Dot (I.Idx (n+1), I.Shift (n+1)), B)
      | abstractGlobalSub (K, I.Dot (I.Idx k, s'), I.Decl (B, T as S.Parameter _)) =
          I.Dot (I.Idx (lookupBV (K, k)), abstractGlobalSub (K, s', B))
      | abstractGlobalSub (K, I.Dot (I.Exp U, s'), I.Decl (B, T as S.Lemma _)) =
          I.Dot (I.Exp (abstractExp (K, 0, (U, I.id))), abstractGlobalSub (K, s', B))



    (* collectGlobalSub (G0, s, B, collect) = collect'

       Invariant:
       If   |- G0 ctx
       and  |- G ctx
       and  G |- B tags
       and  G0 |- s : G
       and  collect is a function which maps
               (d, K)  (d expresses the number of parameters in K, |- K aux ctx)
            to K'      (|- K' aux ctx, which collects all EVars in K)
    *)
    fun collectGlobalSub (G0, I.Shift _, I.Null, collect) =  collect
      | collectGlobalSub (G0, s, B as I.Decl (_, S.Parameter (SOME l)), collect) =
        let
          val F.LabelDec (name, _, G2) = F.labelLookup l
        in
          skip (G0, List.length G2, s, B, collect)
        end
      | collectGlobalSub (G0, I.Dot (I.Exp (U), s), I.Decl (B, T), collect) =
          collectGlobalSub (G0, s, B, fn (d, K) =>
                       collect (d, collectExp (T, d, G0, (U, I.id), K)))
    (* no cases for (G0, s, B as I.Decl (_, S.Parameter NONE), collect) *)


    and skip (G0, 0, s, B, collect) = collectGlobalSub (G0, s, B, collect)
      | skip (I.Decl (G0, D), n, s, I.Decl (B, T as S.Parameter _), collect) =
          skip (G0, n-1, I.invDot1 s, B, fn (d, K) => collect (d+1, I.Decl (K, BV (D, T))))


    (* abstractNew ((G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- G0 ctx
       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, Gp, G2
       and  G' |- B' tags
       and  G' |- s' : G
    *)
    fun abstractNew ((G0, B0), s, B) =
        let
          val cf = collectGlobalSub (G0, s, B, fn (_, K') => K')
          val K = cf (0, I.Null)
        in
          (abstractCtx K, abstractGlobalSub (K, s, B))
        end




    (* abstractSub (t, B1, (G0, B0), s, B) = ((G', B'), s')

       Invariant:
       If   . |- t : G1
       and  G1 |- B1 tags

       and  G0 |- B0 tags
       and  G0 |- s : G
       and  G |- B tags
       then . |- G' = G1, G0, G2
       and  B' |- G' tags
       and  G' |- s' : G
    *)
    fun abstractSubAll (t, B1, (G0, B0), s, B) =
        let
          (* skip'' (K, (G, B)) = K'

             Invariant:
             If   G = x1:V1 .. xn:Vn
             and  G |- B = <param> ... <param> tags
             then  K' = K, BV (x1) .. BV (xn)
          *)

          fun skip'' (K, (I.Null, I.Null)) = K
            | skip'' (K, (I.Decl (G0, D), I.Decl(B0, T))) = I.Decl (skip'' (K, (G0, B0)), BV (D, T))

          val collect2 = collectGlobalSub (G0, s, B, fn (_, K') => K')
          val collect0 = collectGlobalSub (I.Null, t, B1, fn (_, K') => K')
          val K0 = collect0 (0, I.Null)
          val K1 = skip'' (K0, (G0, B0))
          val d = I.ctxLength G0
          val K = collect2 (d, K1)
        in
          (abstractCtx K, abstractGlobalSub (K, s, B))
        end




    (* abstractFor (K, depth, (F, s)) = F'
       F' = {{F[s]}}_K

       Invariant:
       If    G |- s : G1     G1 |- U : V    (U,s) is in whnf
       and   K is internal context in dependency order
       and   |G| = depth
       and   K ||- U and K ||- V
       then  {{K}}, G |- U' : V'
       and   . ||- U' and . ||- V'
       and   U' is in nf
    *)

    fun abstractFor (K, depth, (F.All (F.Prim D, F), s)) =
          F.All (F.Prim (abstractDec (K, depth, (D, s))),
                 abstractFor (K, depth+1, (F, I.dot1 s)))
      | abstractFor (K, depth, (F.Ex (D, F), s)) =
          F.Ex (abstractDec (K, depth, (D, s)),
                abstractFor (K, depth+1, (F, I.dot1 s)))
      | abstractFor (K, depth, (F.True, s)) = F.True
      | abstractFor (K, depth, (F.And (F1, F2), s)) =
          F.And (abstractFor (K, depth, (F1, s)),
                 abstractFor (K, depth, (F2, s)))

    (* abstract (Gx, F) = F'

       Invariant:
       If   G, Gx |- F formula
       then G |- F' = {{Gx}} F formula
    *)
    fun allClo (I.Null, F) = F
      | allClo (I.Decl (Gx, D), F) = allClo (Gx, F.All (F.Prim D, F))



    fun convert (I.Null) = I.Null
      | convert (I.Decl (G, D)) = I.Decl (convert G, BV (D, S.Parameter NONE))


    fun createEmptyB 0 = I.Null
      | createEmptyB (n) = I.Decl (createEmptyB (n-1), S.None)


    fun lower (_, 0) = I.Null
      | lower (I.Decl (G, D), n) = I.Decl (lower (G, n-1), D)


    fun split (G, 0) = (G, I.Null)
      | split (I.Decl (G, D), n) =
        let
          val (G1, G2) = split (G, n-1)
        in
          (G1, I.Decl (G2, D))
        end





    (* shift G = s'

       Invariant:
       Forall contexts G0:
       If   |- G0, G ctx
       then G0, V, G |- s' : G0, G
    *)

    fun shift (I.Null) = I.shift
      | shift (I.Decl (G, _)) = I.dot1 (shift G)



    (* ctxSub (G, s) = G'

       Invariant:
       If   G2 |- s : G1
       and  G1 |- G ctx
       then G2 |- G' = G[s] ctx
    *)

    fun ctxSub (nil, s) = nil
      | ctxSub (D :: G, s) = I.decSub (D, s) :: ctxSub (G, I.dot1 s)


    (* weaken2 (G, a, i, S) = w'

       Invariant:
       G |- w' : Gw
       Gw < G
       G |- S : {Gw} V > V
    *)
    fun weaken2 (I.Null, a, i) = (I.id, fn S => S)
      | weaken2 (I.Decl (G', D as I.Dec (name, V)), a, i) =
        let
          val (w', S') = weaken2 (G', a, i+1)
        in
          if Subordinate.belowEq (I.targetFam V, a) then
            (I.dot1 w', fn S => I.App (I.Root (I.BVar i, I.Nil), S))
          else (I.comp (w', I.shift), S')
        end


    (* raiseType (G, V) = {{G}} V

       Invariant:
       If G |- V : L
       then  . |- {{G}} V : L

       All abstractions are potentially dependent.
    *)
    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id), I.Maybe), V))

    (* raiseFor (G, F, w, sc) = F'

       Invariant:
       If   G0 |- G ctx
       and  G0, G, GF |- F for
       and  G0, {G} GF [...] |- w : G0
       and  sc maps  (G0, GA |- w : G0, |GA|)  to   (G0, GA, G[..] |- s : G0, G, GF)
       then G0, {G} GF |- F' for
    *)
    fun raiseFor (k, Gorig,  F as F.True, w, sc) = F
      | raiseFor (k, Gorig, F.Ex (I.Dec (name, V), F), w, sc) =
        let
          val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
          val g = I.ctxLength G
          val s = sc (w, k)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)
          val V' = I.EClo (V, s)
                                        (* G0, {G}GF[..], G |- V' : type *)
          val (nw, S) = weaken2 (G, I.targetFam V, 1)
                                        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)

          val iw = Whnf.invert nw
                                        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
          val Gw = Whnf.strengthen (iw, G)
                                        (* Generalize the invariant for Whnf.strengthen --cs *)
          val V'' = Whnf.normalize (V', iw)
                                        (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
          val V''' = Whnf.normalize (raiseType (Gw, V''), I.id)
                                        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
          val S''' = S I.Nil
                                        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)

          val sc' = fn (w', k') =>
                      let
                                        (* G0, GA |- w' : G0 *)
                        val s' = sc (w', k')
                                        (* G0, GA, G[..] |- s' : G0, G, GF *)
                      in
                        I.Dot (I.Exp (I.Root (I.BVar (g+k'-k), S''')), s')
                                        (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
                      end
          val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
        in
          F.Ex (I.Dec (name, V'''), F')
        end

      | raiseFor (k, Gorig, F.All (F.Prim (I.Dec (name, V)), F), w, sc) =
        let
(*                val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
                  val g = I.ctxLength G
                  val s = sc (w, k)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)
                  val V' = Whnf.normalize (raiseType (G, Whnf.normalize (V, s)), I.id)
                                        (* G0, {G}GF[..] |- V' = {G}(V[s]) : type *)
                  val S' = spine g
                                        (* G0, {G}GF[..] |- S' > {G}(V[s]) > V[s] *)
                  val sc' = fn (w', k') =>
                              let
                                        (* G0, GA |- w' : G0 *)
                                val s' = sc (w', k')
                                        (* G0, GA, G[..] |- s' : G0, G, GF *)
                              in
                                I.Dot (I.Exp (I.Root (I.BVar (g + k'-k), S')), s')
                                        (* G0, GA, G[..] |- g+k'-k. S', s' : G0, G, GF, V *)
                              end
                  val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
                in
                  F.All (F.Prim (I.Dec (name, V')), F')
*)
          val G = F.listToCtx (ctxSub (F.ctxToList Gorig, w))
          val g = I.ctxLength G
          val s = sc (w, k)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)
          val V' = I.EClo (V, s)
                                        (* G0, {G}GF[..], G |- V' : type *)
          val (nw, S) = weaken2 (G, I.targetFam V, 1)
                                        (* G0, {G}GF[..], G |- nw : G0, {G}GF[..], Gw
                                         Gw < G *)

          val iw = Whnf.invert nw
                                        (* G0, {G}GF[..], Gw |- iw : G0, {G}GF[..], G *)
          val Gw = Whnf.strengthen (iw, G)
                                        (* Generalize the invariant for Whnf.strengthen --cs *)
          val V'' = Whnf.normalize (V', iw)
                                        (* G0, {G}GF[..], Gw |- V'' = V'[iw] : type*)
          val V''' = Whnf.normalize (raiseType (Gw, V''), I.id)
                                        (* G0, {G}GF[..] |- V''' = {Gw} V'' : type*)
          val S''' = S I.Nil
                                        (* G0, {G}GF[..], G[..] |- S''' : {Gw} V''[..] > V''[..] *)
                                        (* G0, {G}GF[..], G |- s : G0, G, GF *)

          val sc' = fn (w', k') =>
                      let
                                        (* G0, GA |- w' : G0 *)
                        val s' = sc (w', k')
                                        (* G0, GA, G[..] |- s' : G0, G, GF *)
                      in
                        I.Dot (I.Exp (I.Root (I.BVar (g+k'-k), S''')), s')
                                        (* G0, GA, G[..] |- (g+k'-k). S', s' : G0, G, GF, V *)
                      end
          val F' = raiseFor (k+1, Gorig, F, I.comp (w, I.shift), sc')
        in
          F.All(F.Prim (I.Dec (name, V''')), F')
        end
    (* the other case of F.All (F.Block _, _) is not yet covered *)


    fun extend (K, nil) = K
      | extend (K, D :: L) = extend (I.Decl (K, BV (D, S.None)), L)

    (* makeFor (G, w, AF) = F'

       Invariant :
       If   |- G ctx
       and  G |- w : G'
       and  G' |- AF approx for
       then G'; . |- F' = {EVARS} AF  for
    *)

    fun makeFor (K, w, Head (G, (F, s), d)) =
        let
          val cf = collectGlobalSub (G, s, createEmptyB d, fn (_, K') => K')
          val k = I.ctxLength K
          val K' = cf (I.ctxLength G, K)
          val k' = I.ctxLength K'
          val (GK, BK) = abstractCtx K'
          val _ = if !Global.doubleCheck then TypeCheck.typeCheckCtx (GK) else ()
(*        val _ = if !Global.doubleCheck then checkTags (GK, BK) else () *)
          val w' = I.comp (w, I.Shift (k'-k))
          val FK = abstractFor (K', 0, (F, s))
          val _ = if !Global.doubleCheck then FunTypeCheck.isFor (GK, FK) else ()
          val (GK1, GK2) = split (GK, k'-k)
        in
          (GK1, allClo (GK2, FK))
        end
      | makeFor (K, w, Block ((G, t, d, G2), AF)) =
        let
          val k = I.ctxLength K
          val collect = collectGlobalSub (G, t, createEmptyB d, fn (_, K') => K')
          val K' = collect (I.ctxLength G, K)   (* BUG *)
          val k' = I.ctxLength K'
          val K'' = extend (K', G2)
          val w' = F.dot1n (F.listToCtx G2, I.comp (w, I.Shift (k'-k)))
          val (GK, F') = makeFor (K'', w', AF)
          val _ = if !Global.doubleCheck then FunTypeCheck.isFor (GK, F') else ()
          val (GK1, GK2) = split (GK, List.length G2)
          val F'' = raiseFor (0, GK2, F', I.id, fn (w, _) => F.dot1n (GK2, w))
          val _ = if !Global.doubleCheck then FunTypeCheck.isFor (GK1, F'') else ()
          val (GK11, GK12) = split (GK1, k' - k)
          val F''' = allClo (GK12, F'')
          val _ = if !Global.doubleCheck then FunTypeCheck.isFor (GK11, F''') else ()
        in
          (GK11, F''')
        end

    fun abstractApproxFor (AF as Head (G, _, _)) =
        let
          val (_, F) = makeFor (convert G, I.id, AF)
        in
          F
        end
      | abstractApproxFor (AF as Block ((G, _, _, _), _)) =
        let
          val (_, F) = makeFor (convert G, I.id, AF)
        in
          F
        end

  in
    val weaken = weaken
    val raiseType = raiseType

    val abstractSub = abstractSubAll
    val abstractSub' = abstractNew

    val abstractApproxFor = abstractApproxFor
  end

end;  (* functor MTPAbstract *)
