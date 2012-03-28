(* Convertibility Modulo Beta and Eta *)
(* Author: Frank Pfenning, Carsten Schuermann *)

functor Conv
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf   : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
     )
     : CONV =
struct
  (*! structure IntSyn = IntSyn' !*)

  local
    open IntSyn

    (* eqUni (L1, L2) = B iff L1 = L2 *)
    fun eqUni (Type, Type) = true
      | eqUni (Kind, Kind) = true
      | eqUni _ = false

    (* convExpW ((U1, s1), (U2, s2)) = B

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1) in whnf
            G |- s2 : G2    G2 |- U2 : V2    (U2,s2) in whnf
            G |- V1[s1] == V2[s2] == V : L
       then B iff G |- U1[s1] == U2[s2] : V

       Effects: EVars may be lowered
    *)
    fun convExpW ((Uni(L1), _), (Uni(L2), _)) =
          eqUni (L1, L2)

      | convExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
          (* s1 = s2 = id by whnf invariant *)
          (* order of calls critical to establish convSpine invariant *)
          (case (H1, H2) of
             (BVar(k1), BVar(k2)) =>
               (k1 = k2) andalso convSpine ((S1, s1), (S2, s2))
           | (Const(c1), Const(c2)) =>
               (c1 = c2) andalso convSpine ((S1, s1), (S2, s2))
           | (Skonst c1, Skonst c2) =>
               (c1 = c2) andalso convSpine ((S1, s1), (S2, s2))
           | (Proj (Bidx v1, i1), Proj (Bidx v2, i2)) =>
               (v1 = v2) andalso (i1 = i2) andalso convSpine ((S1, s1), (S2, s2))
           | (FVar (n1,_,s1'), FVar (n2,_,s2')) =>
               (* s1' = s2' = ^|G| *)
               (n1 = n2) andalso convSpine ((S1, s1), (S2, s2))
           | (FgnConst (cs1, cD1), FgnConst (cs2, cD2)) =>
               (* they must have the same string representation *)
               (cs1 = cs2) andalso (conDecName (cD1) = conDecName (cD2))
               andalso convSpine ((S1, s1), (S2, s2))
           | (Def (d1), Def (d2)) =>
               (* because of strict *)
               ((d1 = d2) andalso convSpine ((S1, s1), (S2, s2)))
               orelse convExpW (Whnf.expandDef (Us1), Whnf.expandDef (Us2))
           | (Def (d1), _) => convExpW (Whnf.expandDef Us1, Us2)
           | (_, Def(d2)) => convExpW (Us1, Whnf.expandDef Us2)
           | _ => false)

      | convExpW ((Pi (DP1, V1), s1), (Pi (DP2, V2), s2)) =
          convDecP ((DP1, s1), (DP2, s2))
          andalso convExp ((V1, dot1 s1), (V2, dot1 s2))

      | convExpW (Us1 as (Pi _, _), Us2 as (Root (Def _, _), _)) =
          convExpW (Us1, Whnf.expandDef Us2)

      | convExpW (Us1 as (Root (Def _, _), _), Us2 as (Pi _, _)) =
          convExpW (Whnf.expandDef Us1, Us2)

      | convExpW ((Lam (D1, U1), s1), (Lam (D2, U2), s2)) =
        (* G |- D1[s1] = D2[s2] by typing invariant *)
          convExp ((U1, dot1 s1),  (U2, dot1 s2))

      | convExpW ((Lam (D1, U1), s1), (U2, s2)) =
          convExp ((U1, dot1 s1),
                   (Redex (EClo (U2, shift),
                           App (Root (BVar (1), Nil), Nil)), dot1 s2))

      | convExpW ((U1,s1), (Lam(D2, U2) ,s2)) =
          convExp ((Redex (EClo (U1, shift),
                           App (Root (BVar (1), Nil), Nil)), dot1 s1),
                   (U2, dot1 s2))

      | convExpW ((FgnExp csfe1, s1), Us2) = (* s1 = id *)
          FgnExpStd.EqualTo.apply csfe1 (EClo Us2)

      | convExpW (Us1, (FgnExp csfe2, s2)) = (* s2 = id *)
          FgnExpStd.EqualTo.apply csfe2 (EClo Us1)

      | convExpW ((EVar (r1, _, _, _), s1), (EVar(r2, _, _, _), s2)) =
          (r1 = r2) andalso convSub (s1, s2)

      (* ABP -- 2/18/03 Added missing case*)
      (* Note that under Head, why is NSDef never used?? *)
      | convExpW _ = false
        (* Possible are:
           L <> Pi D. V   Pi D. V <> L
           X <> U         U <> X
        *)

    (* convExp ((U1, s1), (U2, s2)) = B

       Invariant:
       as above, but (U1, s1), (U2, s2) need not to be in whnf
       Effects: EVars may be lowered
    *)
    and convExp (Us1, Us2) = convExpW (Whnf.whnf Us1, Whnf.whnf Us2)

    (* convSpine ((S1, s1), (S2, s2)) = B

       Invariant:
       If   G |- s1 : G1     G1 |- S1 : V1 > W1
            G |- s2 : G2    G2 |- S2 : V2 > W2
            G |- V1[s1] = V2[s2] = V : L
            G |- W1[s1] = W2[s2] = W : L
       then B iff G |- S1 [s1] = S2 [s2] : V > W

       Effects: EVars may be lowered
    *)
    and convSpine ((Nil, _), (Nil, _)) = true
      | convSpine ((App (U1, S1), s1), (App (U2, S2), s2)) =
          convExp ((U1, s1), (U2, s2)) andalso convSpine ((S1, s1), (S2, s2))
      | convSpine ((SClo (S1, s1'), s1), Ss2) =
          convSpine ((S1, comp (s1', s1)), Ss2)
      | convSpine (Ss1, (SClo (S2, s2'), s2)) =
          convSpine (Ss1, (S2, comp (s2', s2)))
      | convSpine (_ , _) = false (* bp*)
    (* no others are possible due to typing invariants *)

    (* convSub (s1, s2) = B

     Invariant:
     If  G |- s1 : G'
         G |- s2 : G'
     then B iff G |- s1 = s2 : G'
     Effects: EVars may be lowered
    *)
    and convSub (Shift(n), Shift(m)) = true (* n = m by invariants *)
      | convSub (Shift(n), s2 as Dot _) =
          convSub (Dot(Idx(n+1), Shift(n+1)), s2)
      | convSub (s1 as Dot _, Shift(m)) =
          convSub (s1, Dot(Idx(m+1), Shift(m+1)))
      | convSub (Dot(Ft1,s1), Dot(Ft2,s2)) =
          (case (Ft1, Ft2) of
             (Idx (n1), Idx (n2)) => (n1 = n2)
           | (Exp (U1), Exp (U2)) => convExp ((U1, id), (U2, id))
           | (Block (Bidx k1), Block (Bidx k2)) => (k1 = k2) (* other block cases don't matter -cs 2/18/03 *)
           | (Exp (U1), Idx (n2)) => convExp ((U1, id), (Root (BVar (n2), Nil), id))
           | (Idx (n1), Exp (U2)) => convExp ((Root (BVar (n1), Nil), id), (U2, id))
           | (Undef, Undef) => true
           | _ => false)
          andalso convSub (s1, s2)

    (* convDec ((x1:V1, s1), (x2:V2, s2)) = B

       Invariant:
       If   G |- s1 : G'     G'  |- V1 : L
            G |- s2 : G''    G'' |- V2 : L
       then B iff G |- V1 [s1]  = V2 [s2] : L
       Effects: EVars may be lowered
    *)
    and convDec ((Dec (_, V1), s1), (Dec (_, V2), s2)) =  convExp ((V1, s1), (V2, s2))
      | convDec ((BDec(_, (c1, s1)), t1), (BDec (_, (c2, s2)), t2)) =
          c1 = c2 andalso convSub (comp (s1, t1), comp (s2, t2))

    (* convDecP see convDec *)
    and convDecP (((D1, P1), s1), ((D2, P2), s2)) =  convDec ((D1, s1), (D2, s2))

  in
    val conv = convExp
    val convDec = convDec
    val convSub = convSub
  end (* local *)
end;  (* functor Conv *)
