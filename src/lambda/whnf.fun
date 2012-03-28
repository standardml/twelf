(* Weak Head-Normal Forms *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

functor Whnf ((*! structure IntSyn' : INTSYN !*)
               )
  : WHNF =
struct
  (*! structure IntSyn = IntSyn' !*)

  (*
     Weak Head-Normal Form (whnf)

     whnf ::= (L, s) | (Pi DP. U, s) | (Root (#k(b), S))
            | (Root(n,S), id) | (Root(c,S), id) | (Root(d,S), id) | (Root(F[s'], S), id)
            | (Root(fgnC,S), id) where fgnC is a foreign constant
            | (Lam D. U, s) | (X, s) where X is uninstantiated, X of base type
                                     during type reconstruction, X might have variable type
            | (FgnExp, id) where FgnExp is a foreign expression

     Normal Form (nf)

        UA ::= L | Pi (DA,P). UA
             | Root(n,SA) | Root(c,SA) | Root(d,SA) | Root(fgnC,SA) | Root (#k(b), S)
             | Lam DA. UA | FgnExp
        DA ::= x:UA
        SA ::= Nil | App (UA, SA)

     Existential Normal Form (enf)

     Existential normal forms are like normal forms, but also allows
     X[s] where X is uninstantiated with no particular restriction on s
     or type of X.

     An existential normal form is a hereditary weak head-normal form.
  *)

  local
    open IntSyn


    (* exception Undefined *)

    exception Eta

    (* etaContract (U, s, n) = k'

       Invariant:
       if   G, V1, .., Vn |- s : G1  and  G1 |- U : V
       then if   lam V1...lam Vn. U[s] =eta*=> k
            then k' = k
            and  G |- k' : Pi V1...Pi Vn. V [s]
            else Eta is raised
              (even if U[s] might be eta-reducible to some other expressions).
    *)
    (* optimization(?): quick check w/o substitution first *)
    fun etaContract (Root (BVar(k), S), s, n) =
        (case bvarSub (k, s)
           of Idx (k') => if k' > n
                            then (etaContract' (S, s, n); k'-n)
                          else raise Eta
            | _ => raise Eta)
      | etaContract (Lam (D, U), s, n) =
          etaContract (U, dot1 s, n+1)
      | etaContract (EClo (U, s'), s, n) =
          etaContract (U, comp (s', s), n)
      | etaContract (EVar (ref (SOME(U)), _, _, _), s, n) =
          etaContract (U, s, n)
      | etaContract (AVar (ref (SOME(U))), s, n) =
          etaContract (U, s, n)
      | etaContract _ = raise Eta
        (* Should fail: (c@S), (d@S), (F@S), X *)
        (* Not treated (fails): U@S *)
        (* Could weak head-normalize for more thorough checks *)
        (* Impossible: L, Pi D.V *)

    (* etaContract' (S, s, n) = R'

       Invariant:
       If  G |- s : G1    and  G1 |- S : V > W
       then if   S[s] =eta*=> n ; n-1 ; ... ; 1 ; Nil
            then ()
       else Eta is raised
    *)
    and etaContract' (Nil, s, 0) = ()
      | etaContract' (App(U, S), s, n) =
          if etaContract (U, s, 0) = n
            then etaContract' (S, s, n-1)
          else raise Eta
      | etaContract' (SClo (S, s'), s, n) =
          etaContract' (S, comp (s', s), n)
      | etaContract' _ = raise Eta

    (* dotEta (Ft, s) = s'

       Invariant:
       If   G |- s : G1, V  and G |- Ft : V [s]
       then Ft  =eta*=>  Ft1
       and  s' = Ft1 . s
       and  G |- s' : G1, V
    *)
    fun dotEta (Ft as Idx _, s) = Dot (Ft, s)
      | dotEta (Ft as Exp (U), s) =
        let
          val Ft' = Idx (etaContract (U, id, 0))
                   handle Eta => Ft
        in
          Dot (Ft', s)
        end
      | dotEta (Ft as Undef, s) = Dot (Ft, s)


    (* appendSpine ((S1, s1), (S2, s2)) = S'

       Invariant:
       If    G |- s1 : G1   G1 |- S1 : V1' > V1
       and   G |- s2 : G2   G2 |- S2 : V2  > V2'
       and   G |- V1 [s1] == V2 [s2]
       then  G |- S' : V1' [s1] > V2' [s2]
    *)
    fun appendSpine ((Nil, s1), Ss2) = SClo Ss2
      | appendSpine ((App (U1, S1), s1), Ss2) =
          App (EClo (U1, s1), appendSpine ((S1, s1), Ss2))
      | appendSpine ((SClo (S1, s1'), s1), Ss2) =
          appendSpine ((S1, comp(s1', s1)), Ss2)

    (* whnfRedex ((U, s1), (S, s2)) = (U', s')

       Invariant:
       If    G |- s1 : G1   G1 |- U : V1,   (U,s1) whnf
             G |- s2 : G2   G2 |- S : V2 > W2
             G |- V1 [s1] == V2 [s2] == V : L
       then  G |- s' : G',  G' |- U' : W'
       and   G |- W'[s'] == W2[s2] == W : L
       and   G |- U'[s'] == (U[s1] @ S[s2]) : W
       and   (U',s') whnf

       Effects: EVars may be lowered to base type.
    *)
    fun whnfRedex (Us, (SClo (S, s2'), s2)) =
          whnfRedex (Us, (S, comp (s2', s2)))
      | whnfRedex (Us as (Root R, s1), (Nil, s2)) = Us
      | whnfRedex ((Root (H1, S1), s1), (S2, s2)) =
          (* S2 = App _, only possible if term is not eta-expanded *)
          (Root (H1, appendSpine ((S1, s1), (S2, s2))), id)
      | whnfRedex ((Lam (_, U1), s1), (App (U2, S), s2)) =
          whnfRedex (whnf (U1, dotEta (frontSub (Exp (U2), s2), s1)), (S, s2))
      | whnfRedex (Us as (Lam _, s1), _) = Us  (* S2[s2] = Nil *)
      | whnfRedex (Us as (EVar _, s1), (Nil, s2)) = Us
      | whnfRedex (Us as (X as EVar _, s1), Ss2) =
          (* Ss2 must be App, since prior cases do not apply *)
          (* lowerEVar X results in redex, optimize by unfolding call to whnfRedex *)
          (lowerEVar X; whnfRedex (whnf Us, Ss2))
      | whnfRedex (Us as (AVar(ref (SOME U)), s1), Ss2) =
          whnfRedex((U,s1), Ss2)
      | whnfRedex (Us as (AVar(ref NONE), s1), Ss2) = Us
      | whnfRedex (Us as (FgnExp _, _), _) = Us
      (* Uni and Pi can arise after instantiation of EVar X : K *)
      | whnfRedex (Us as (Uni _, s1), _) = Us   (* S2[s2] = Nil *)
      | whnfRedex (Us as (Pi _, s1), _) = Us    (* S2[s2] = Nil *)
      (* Other cases impossible since (U,s1) whnf *)

    (* lowerEVar' (G, V[s]) = (X', U), see lowerEVar *)
    and lowerEVar' (G, (Pi ((D',_), V'), s')) =
        let
          val D'' = decSub (D', s')
          val (X', U) = lowerEVar' (Decl (G, D''), whnfExpandDef (V', dot1 s'))
        in
          (X', Lam (D'', U))
        end
      | lowerEVar' (G, Vs') =
        let
          val X' = newEVar (G, EClo Vs')
        in
          (X', X')
        end
    (* lowerEVar1 (X, V[s]), V[s] in whnf, see lowerEVar *)
    and lowerEVar1 (EVar (r, G, _, _), Vs as (Pi _, _)) =
        let
          val (X', U) = lowerEVar' (G, Vs)
          val _ = r := SOME (U)
        in
          X'
        end
      | lowerEVar1 (X, _) = X

    (* lowerEVar (X) = X'

       Invariant:
       If   G |- X : {{G'}} P
            X not subject to any constraints
       then G, G' |- X' : P

       Effect: X is instantiated to [[G']] X' if G' is empty
               otherwise X = X' and no effect occurs.
    *)
    and lowerEVar (X as EVar (r, G, V, ref nil)) = lowerEVar1 (X, whnfExpandDef (V, id))
      | lowerEVar (EVar _) =
        (* It is not clear if this case can happen *)
        (* pre-Twelf 1.2 code walk, Fri May  8 11:05:08 1998 *)
        raise Error "Typing ambiguous -- constraint of functional type cannot be simplified"


    (* whnfRoot ((H, S), s) = (U', s')

       Invariant:
       If    G |- s : G1      G1 |- H : V
                              G1 |- S : V > W
       then  G |- s' : G'     G' |- U' : W'
       and   G |- W [s] = W' [s'] : L

       Effects: EVars may be instantiated when lowered
    *)
    and whnfRoot ((BVar (k), S), s)   =
        (case bvarSub (k, s)
           of Idx (k) => (Root (BVar (k), SClo (S, s)), id)
            | Exp (U) => whnfRedex (whnf (U, id), (S, s)))
      (* Undef should be impossible *)
      | whnfRoot ((Proj (B as Bidx _, i), S), s) =
         (* could blockSub (B, s) return instantiated LVar ? *)
         (* Sat Dec  8 13:43:17 2001 -fp !!! *)
         (* yes Thu Dec 13 21:48:10 2001 -fp !!! *)
         (* was: (Root (Proj (blockSub (B, s), i), SClo (S, s)), id) *)
        (case blockSub (B, s)
           of B' as Bidx (k) => (Root (Proj (B', i), SClo (S, s)), id)
            | B' as LVar _ => whnfRoot ((Proj (B', i), SClo (S, s)), id)
            | Inst L => whnfRedex (whnf (List.nth (L, i-1), id), (S, s)))
      | whnfRoot ((Proj (LVar (ref (SOME B), sk, (l, t)), i), S), s) =
         whnfRoot ((Proj (blockSub (B, comp (sk, s)), i), SClo (S, s)), id)
      | whnfRoot ((Proj (L as LVar (r, sk, (l, t)), i), S), s) = (* r = ref NONE *)
         (Root (Proj (LVar (r, comp (sk, s), (l, t)), i), SClo (S, s)), id)
         (* scary: why is comp(sk, s) = ^n ?? -fp July 22, 2010, -fp -cs *)
        (* was:
         (Root (Proj (LVar (r, comp (sk, s), (l, comp(t, s))), i), SClo (S, s)), id)
         Jul 22, 2010 -fp -cs
         *)
         (* do not compose with t due to globality invariant *)
         (* Thu Dec  6 20:34:30 2001 -fp !!! *)
         (* was: (Root (Proj (L, i), SClo (S, s)), id) *)
         (* going back to first version, because globality invariant *)
         (* no longer satisfied Wed Nov 27 09:49:58 2002 -fp *)
      (* Undef and Exp should be impossible by definition of substitution -cs *)
      | whnfRoot ((FVar (name, V, s'), S), s) =
         (Root (FVar (name, V, comp (s', s)), SClo (S, s)), id)
      | whnfRoot ((NSDef (d), S), s) =
          whnfRedex (whnf (IntSyn.constDef d, id), (S, s))
      | whnfRoot ((H, S), s) =
         (Root (H, SClo (S, s)), id)

    (* whnf (U, s) = (U', s')

       Invariant:
       If    G |- s : G'    G' |- U : V
       then  G |- s': G''   G''|- U' : V'
       and   G |- V [s] == V' [s'] == V'' : L
       and   G |- U [s] == U' [s'] : V''
       and   (U', s') whnf
    *)
    (*
       Possible optimization :
         Define whnf of Root as (Root (n , S [s]), id)
         Fails currently because appendSpine does not necessairly return a closure  -cs
         Advantage: in unify, abstract... the spine needn't be treated under id, but under s
    *)
    and whnf (U as Uni _, s) = (U,s)
      | whnf (U as Pi _, s) = (U,s)
      (* simple optimization (C@S)[id] = C@S[id] *)
      (* applied in Twelf 1.1 *)
      (* Sat Feb 14 20:53:08 1998 -fp *)
(*      | whnf (Us as (Root _, Shift (0))) = Us*)
      (* commented out, because non-strict definitions slip
         Mon May 24 09:50:22 EDT 1999 -cs  *)
      | whnf (Root R, s) =  whnfRoot (R, s)
      | whnf (Redex (U, S), s) =  whnfRedex (whnf (U, s), (S, s))
      | whnf (Us as (Lam _, s)) = Us
      | whnf (AVar (ref (SOME U)), s) =  whnf (U, s)
      | whnf (Us as (AVar _, s)) =  Us
      | whnf (EVar (ref (SOME U), _, _, _), s) = whnf (U, s)
      (* | whnf (Us as (EVar _, s)) = Us *)
      (* next two avoid calls to whnf (V, id), where V is type of X *)
      | whnf (Us as (EVar (r, _, Root _, _), s)) =  Us
      | whnf (Us as (EVar (r, _, Uni _, _), s)) =  Us
      | whnf (Us as (X as EVar (r, _, V, _), s)) =
          (case whnf (V, id)
             of (Pi _, _) => (lowerEVar X; whnf Us)
                             (* possible opt: call lowerEVar1 *)
              | _ => Us)
      | whnf (EClo (U, s'), s) = whnf (U, comp (s', s))
      | whnf (Us as (FgnExp _, Shift (0))) = Us
      | whnf (Us as (FgnExp csfe , s)) =
          (FgnExpStd.Map.apply csfe (fn U => EClo (U, s)), id)

    (* expandDef (Root (Def (d), S), s) = (U' ,s')

       Invariant:
       If    G |- s : G1     G1 |- S : V > W            ((d @ S), s) in whnf
                             .  |- d = U : V'
       then  G |- s' : G'    G' |- U' : W'
       and   G |- V' == V [s] : L
       and   G |- W' [s'] == W [s] == W'' : L
       and   G |- (U @ S) [s] == U' [s'] : W'
       and   (U', s') in whnf
    *)

    and expandDef (Root (Def (d), S), s) =
          (* why the call to whnf?  isn't constDef (d) in nf? -kw *)
          whnfRedex (whnf (constDef (d), id), (S, s))

    and whnfExpandDefW (Us as (Root (Def _, _), _)) = whnfExpandDefW (expandDef Us)
      | whnfExpandDefW Us = Us
    and whnfExpandDef Us = whnfExpandDefW (whnf Us)

    fun newLoweredEVarW (G, (Pi ((D, _), V), s)) =
        let
          val D' = decSub (D, s)
        in
          Lam (D', newLoweredEVar (Decl (G, D'), (V, dot1 s)))
        end
      | newLoweredEVarW (G, Vs) = newEVar (G, EClo Vs)

    and newLoweredEVar (G, Vs) = newLoweredEVarW (G, whnfExpandDef Vs)

    fun newSpineVarW (G, (Pi ((Dec (_, Va), _), Vr), s)) =
        let
          val X = newLoweredEVar (G, (Va, s))
        in
          App (X, newSpineVar (G, (Vr, dotEta (Exp (X), s))))
        end
      | newSpineVarW (G, _) = Nil

    and newSpineVar (G, Vs) = newSpineVarW (G, whnfExpandDef Vs)

    fun spineToSub (Nil, s) = s
      | spineToSub (App (U, S), s) = spineToSub (S, dotEta (Exp (U), s))


    (* inferSpine ((S, s1), (V, s2)) = (V', s')

       Invariant:
       If  G |- s1 : G1  and  G1 |- S : V1 > V1'
       and G |- s2 : G2  and  G2 |- V : L,  (V, s2) in whnf
       and G |- S[s1] : V[s2] > W  (so V1[s1] == V[s2] and V1[s1] == W)
       then G |- V'[s'] = W
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    fun inferSpine ((Nil, _), Vs) = Vs
      | inferSpine ((SClo (S, s'), s), Vs) =
          inferSpine ((S, comp (s', s)), Vs)
      | inferSpine ((App (U, S), s1), (Pi (_, V2), s2)) =
          inferSpine ((S, s1), whnfExpandDef (V2, Dot (Exp (EClo (U, s1)), s2)))

    (* inferCon (C) = V  if C = c or C = d or C = sk and |- C : V *)
    (* FIX: this is almost certainly mis-design -kw *)
    fun inferCon (Const (cid)) = constType (cid)
      | inferCon (Skonst (cid)) = constType (cid)
      | inferCon (Def (cid)) = constType (cid)

    (* etaExpand' (U, (V,s)) = U'

       Invariant :
       If    G |- U : V [s]   (V,s) in whnf
       then  G |- U' : V [s]
       and   G |- U == U' : V[s]
       and   (U', id) in whnf and U' in head-eta-long form
    *)
    (* quite inefficient -cs *)
    (* FIX: this is almost certainly mis-design -kw *)
    fun etaExpand' (U, (Root _, s)) = U
      | etaExpand' (U, (Pi ((D, _), V), s)) =
          Lam (decSub (D, s),
               etaExpand' (Redex (EClo (U, shift),
                                  App (Root (BVar (1), Nil), Nil)), whnfExpandDef (V, dot1 s)))

    (* etaExpandRoot (Root(H, S)) = U' where H = c or H = d

       Invariant:
       If   G |- H @ S : V  where H = c or H = d
       then G |- U' : V
       and  G |- H @ S == U'
       and (U',id) in whnf and U' in head-eta-long form
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    fun etaExpandRoot (U as Root(H, S)) =
          etaExpand' (U, inferSpine ((S, id), (inferCon(H), id)))

    (* whnfEta ((U, s1), (V, s2)) = ((U', s1'), (V', s2)')

       Invariant:
       If   G |- s1 : G1  G1 |- U : V1
       and  G |- s2 : G2  G2 |- V : L
       and  G |- V1[s1] == V[s2] : L

       then G |- s1' : G1'  G1' |- U' : V1'
       and  G |- s2' : G2'  G2' |- V' : L'
       and  G |- V1'[s1'] == V'[s2'] : L
       and (U', s1') is in whnf
       and (V', s2') is in whnf
       and (U', s1') == Lam x.U'' if V[s2] == Pi x.V''

       Similar to etaExpand', but without recursive expansion
    *)
    (* FIX: this is almost certainly mis-design -kw *)
    fun whnfEta (Us, Vs) = whnfEtaW (whnf Us, whnf Vs)

    and whnfEtaW (UsVs as (_, (Root _, _))) = UsVs
      | whnfEtaW (UsVs as ((Lam _, _), (Pi _, _))) = UsVs
      | whnfEtaW ((U, s1), Vs2 as (Pi ((D, P), V), s2)) =
          ((Lam (decSub (D, s2),
                 Redex (EClo (U, comp (s1, shift)),
                        App (Root (BVar (1), Nil), Nil))), id), Vs2)

    (* Invariant:

       normalizeExp (U, s) = U'
       If   G |- s : G' and G' |- U : V
       then U [s] = U'
       and  U' in existential normal form

       If (U, s) contain no existential variables,
       then U' in normal formal
    *)
    fun normalizeExp Us = normalizeExpW (whnf Us)

    and normalizeExpW (U as Uni (L), s) = U
      | normalizeExpW (Pi (DP, U), s) =
          Pi (normalizeDecP (DP, s), normalizeExp (U, dot1 s))
      | normalizeExpW (U as Root (H, S), s) = (* s = id *)
          Root (H, normalizeSpine (S, s))
      | normalizeExpW (Lam (D, U), s) =
          Lam (normalizeDec (D, s), normalizeExp (U, dot1 s))
      | normalizeExpW (Us as (EVar _, s)) = EClo Us
      | normalizeExpW (FgnExp csfe , s) =
          FgnExpStd.Map.apply csfe (fn U => normalizeExp (U, s))
      | normalizeExpW (Us as (AVar(ref (SOME(U))) ,s)) =
          normalizeExpW (U,s)
      | normalizeExpW (Us as (AVar _  ,s)) = (print "Normalize  AVAR\n"; raise Error "")


    and normalizeSpine (Nil, s) =
          Nil
      | normalizeSpine (App (U, S), s) =
          App (normalizeExp (U, s), normalizeSpine (S, s))
      | normalizeSpine (SClo (S, s'), s) =
          normalizeSpine (S, comp (s', s))

    and normalizeDec (Dec (xOpt, V), s) = Dec (xOpt, normalizeExp (V, s))
      | normalizeDec (BDec (xOpt, (c, t)), s) =
         BDec (xOpt, (c, normalizeSub (comp (t, s))))
    and normalizeDecP ((D, P), s) = (normalizeDec (D, s), P)

    (* dead code -fp *)
    (* pre-Twelf 1.2 code walk Fri May  8 11:37:18 1998 *)
    (* not any more --cs Wed Jun 19 13:59:56 EDT 2002 *)
    and normalizeSub (s as Shift _) = s
      | normalizeSub (Dot (Ft as Idx _, s)) =
          Dot (Ft, normalizeSub (s))
      | normalizeSub (Dot (Exp U, s)) =
          (* changed to obtain pattern substitution if possible *)
          (* Sat Dec  7 16:58:09 2002 -fp *)
          (* Dot (Exp (normalizeExp (U, id)), normalizeSub s) *)
          dotEta (Exp (normalizeExp (U, id)), normalizeSub s)


    fun normalizeCtx Null = Null
      | normalizeCtx (Decl (G, D)) =
          Decl (normalizeCtx G, normalizeDec (D, id))


    (* invert s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
    fun invert s =
      let
        fun lookup (n, Shift _, p) = NONE
          | lookup (n, Dot (Undef, s'), p) = lookup (n+1, s', p)
          | lookup (n, Dot (Idx k, s'), p) =
            if k = p then SOME n
            else lookup (n+1, s', p)

        fun invert'' (0, si) = si
          | invert'' (p, si) =
            (case (lookup (1, s, p))
               of SOME k => invert'' (p-1, Dot (Idx k, si))
                | NONE => invert'' (p-1, Dot (Undef, si)))

        fun invert' (n, Shift p) = invert'' (p, Shift n)
          | invert' (n, Dot (_, s')) = invert' (n+1, s')
      in
        invert' (0, s)
      end


    (* strengthen (t, G) = G'

       Invariant:
       If   G'' |- t : G    (* and t strsub *)
       then G' |- t : G  and G' subcontext of G
    *)
    fun strengthen (Shift n (* = 0 *), Null) = Null
      | strengthen (Dot (Idx k (* k = 1 *), t), Decl (G, D)) =
        let
          val t' = comp (t, invShift)
        in
          (* G |- D dec *)
          (* G' |- t' : G *)
          (* G' |- D[t'] dec *)
          Decl (strengthen (t', G), decSub (D, t'))
        end
      | strengthen (Dot (Undef, t), Decl (G, D)) =
          strengthen (t, G)
      | strengthen (Shift n, G) =
          strengthen (Dot (Idx (n+1), Shift (n+1)), G)


    (* isId s = B

       Invariant:
       If   G |- s: G', s weakensub
       then B holds
            iff s = id, G' = G
    *)
    fun isId' (Shift(k), k') = (k = k')
      | isId' (Dot (Idx(n), s'), k') =
          n = k' andalso isId' (s', k'+1)
      | isId' _ = false
    fun isId s = isId' (s, 0)

    (* cloInv (U, w) = U[w^-1]

       Invariant:
       If G |- U : V
          G |- w : G'  w weakening subst
          U[w^-1] defined (without pruning or constraints)

       then G' |- U[w^-1] : V[w^-1]
       Effects: None
    *)
    fun cloInv (U, w) = EClo (U, invert w)

    (* cloInv (s, w) = s o w^-1

       Invariant:
       If G |- s : G1
          G |- w : G2  s weakening subst
          s o w^-1 defined (without pruning or constraints)

       then G2 |- s o w^-1 : G1
       Effects: None
    *)
    fun compInv (s, w) = comp (s, invert w)

    (* functions previously in the Pattern functor *)
    (* eventually, they may need to be mutually recursive with whnf *)

    (* isPatSub s = B

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
    fun isPatSub (Shift(k)) = true
      | isPatSub (Dot (Idx (n), s)) =
          let fun checkBVar (Shift(k)) = (n <= k)
                | checkBVar (Dot (Idx (n'), s)) =
                    n <> n' andalso checkBVar (s)
                | checkBVar (Dot (Undef, s)) =
                    checkBVar (s)
                | checkBVar _ = false
          in
            checkBVar s andalso isPatSub s
          end
      | isPatSub (Dot (Undef, s)) = isPatSub s
      | isPatSub _ = false
        (* Try harder, due to bug somewhere *)
        (* Sat Dec  7 17:05:02 2002 -fp *)
        (* false *)
      (* below does not work, because the patSub is lost *)
      (*
          let val (U', s') = whnf (U, id)
          in
            isPatSub (Dot (Idx (etaContract (U', s', 0)), s))
            handle Eta => false
          end
      | isPatSub _ = false
      *)

    (* makePatSub s = SOME(s') if s is convertible to a patSub
                      NONE otherwise

       Invariant:
       If    G |- s : G'
       and   s = n1 .. nm ^k
       then  B iff  n1, .., nm pairwise distinct
               and  ni <= k or ni = _ for all 1 <= i <= m
    *)
    fun mkPatSub (s as Shift(k)) = s
      | mkPatSub (Dot (Idx (n), s)) =
        let
          val s' = mkPatSub s
          fun checkBVar (Shift(k)) = (n <= k)
            | checkBVar (Dot (Idx (n'), s')) =
              n <> n' andalso checkBVar (s')
            | checkBVar (Dot (Undef, s')) =
                    checkBVar (s')
          val _ = checkBVar s'
        in
          Dot (Idx (n), s')
        end
      | mkPatSub (Dot (Undef, s)) = Dot (Undef, mkPatSub s)
      | mkPatSub (Dot (Exp (U), s)) =
        let
          val (U', t') = whnf (U, id)
          val k = (etaContract (U', t', 0)) (* may raise Eta *)
        in
          Dot (Idx (k), mkPatSub s)
        end
      | mkPatSub _ = raise Eta

    fun makePatSub (s) = SOME (mkPatSub (s)) handle Eta => NONE

  in
    val isPatSub = isPatSub
    val makePatSub = makePatSub
    val dotEta = dotEta
    exception Eta = Eta
    val etaContract = (fn U => etaContract (U, id, 0))

    val whnf = whnf

    val expandDef = expandDef
    val whnfExpandDef = whnfExpandDef
    val etaExpandRoot = etaExpandRoot
    val whnfEta = whnfEta
    val lowerEVar = lowerEVar

    val newLoweredEVar = newLoweredEVar
    val newSpineVar = newSpineVar
    val spineToSub = spineToSub

    val normalize = normalizeExp
    val normalizeDec = normalizeDec
    val normalizeCtx = normalizeCtx

    val invert = invert
    val strengthen = strengthen
    val isId = isId

    val cloInv = cloInv
    val compInv = compInv
  end
end;  (* functor Whnf *)
