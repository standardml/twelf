(* Type checking for Tomega *)
(* Author: Carsten Schuermann *)
(* Modified: Yu Liao *)

functor TomegaTypeCheck
  (structure Abstract : ABSTRACT
   structure TypeCheck : TYPECHECK
   structure Conv : CONV
   structure Whnf : WHNF
   structure Print : PRINT
   structure TomegaPrint : TOMEGAPRINT
   structure Subordinate : SUBORDINATE
   structure Weaken : WEAKEN
   structure TomegaAbstract : TOMEGAABSTRACT
       ) : TOMEGATYPECHECK =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure T = Tomega
    structure S = Subordinate
    structure TA = TomegaAbstract

    fun chatter chlev f =
        if !Global.chatter >= chlev
          then print (f ())
        else ()

     fun normalizeHead (T.Const lemma, t) = T.Const lemma
      | normalizeHead (T.Var k, t) =
        (case T.varSub (k, t)
           of T.Idx (k') => T.Var (k'))
        (* no other cases can occur *)


(*    (* inferCon (Psi, (H, t)) = (F', t')

       Invariant:
       If   Psi  |- t : Psi1
       and  Psi1 |- H : F
       then Psi  |- F'[t'] == F[t]
    *)
    fun inferCon (Psi, T.Const lemma) = inferLemma lemma
      | inferCon (Psi, T.Var k) =
          case T.ctxDec (Psi, k) of T.PDec (_, F') => F'
*)

    (* inferSpine (Psi, (S, t1), (F, t2)) = (F', t')

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- S : F' > F''
       and  Psi  |- t2 : Psi2
       and  Psi2 |- F for
       and  Psi  |- F'[t1] == F[t2]
       then Psi  |- F''[t1] == F'[t']
    *)
    fun inferSpine (Psi, S, Ft) = inferSpineW (Psi, S, T.whnfFor Ft)
    and inferSpineW (Psi, T.Nil, (F, t)) = (F, t)
      | inferSpineW (Psi, T.AppExp (M, S), (T.All ((T.UDec (I.Dec (_, A)), _), F), t)) =
        let
          val _ = chatter 4 (fn () => "[appExp")
          val G = T.coerceCtx (Psi)
          val _ = TypeCheck.typeCheck (G, (M, I.EClo (A, T.coerceSub t)))
          val _ = chatter 4 (fn () => "]")
        in
          inferSpine (Psi, S, (F, T.Dot(T.Exp(M), t)))
        end
      | inferSpineW (Psi, T.AppBlock (I.Bidx k, S),
                     (T.All ((T.UDec (I.BDec (_, (cid, s))), _), F2), t2)) =
        let
          val T.UDec (I.BDec(_, (cid', s')))= T.ctxDec(Psi, k)
          val (G', _) = I.conDecBlock (I.sgnLookup cid')
          val _ = if (cid <> cid') then raise Error("Block label incompatible") else ()
          val s'' = T.coerceSub (T.comp (T.embedSub s, t2))
          val _ = Conv.convSub (s', s'')
        in
            inferSpine (Psi, S, (F2, T.Dot(T.Block(I.Bidx k), t2)))
        end
      | inferSpineW (Psi, T.AppPrg (P, S), (T.All ((T.PDec (_, F1, _, _), _), F2), t)) =
        let
            val _ = checkPrg (Psi, (P, (F1, t)))
        in
            inferSpine (Psi, S, (F2, T.dot1 t))
        end
      | inferSpineW (Psi, _, _) = raise Error "applied, but not of function type."


    and inferPrg (Psi, T.Lam (D, P)) =
        let
          val F = inferPrg (I.Decl (Psi, D), P)
        in
          T.All ((D, T.Explicit), F)
        end
      | inferPrg (Psi, T.New P) =
        let
          val T.All ((T.UDec (D as (I.BDec _)), _), F) = inferPrg (Psi, P)
        in
          TA.raiseF (I.Decl (I.Null, D), (F, I.id))
        end
      | inferPrg (Psi, T.PairExp (U, P)) =
        let
          val V = TypeCheck.infer' (T.coerceCtx Psi, U)
          val F = inferPrg (Psi, P)
        in
          T.Ex ((I.Dec (NONE, V), T.Explicit), F)
        end
      | inferPrg (Psi, T.PairBlock (I.Bidx k, P)) =
        (* Blocks T.Inst, and T.LVar excluded for now *)
        let
          val D = I.ctxLookup (T.coerceCtx Psi, k)
          val F = inferPrg (Psi, P)
        in
          T.Ex ((D, T.Explicit), F)
        end
      | inferPrg (Psi, T.PairPrg (P1, P2)) =
        let
          val F1 = inferPrg (Psi, P1)
          val F2 = inferPrg (Psi, P2)
        in
          T.And (F1, F2)
        end
      | inferPrg (Psi, T.Unit) = T.True
      | inferPrg (Psi, T.Var k) = (case T.ctxDec (Psi, k) of T.PDec (_, F', _, _) => F')
      | inferPrg (Psi, T.Const c) = inferLemma c
      | inferPrg (Psi, T.Redex (P, S)) =
        let
          val F1 = inferPrg (Psi, P)
          val F2 = inferSpine (Psi, S, (F1, T.id))
        in
          T.forSub F2
        end
      | inferPrg (Psi, T.Rec (D as T.PDec (_, F, _, _), P)) =
        let
          val _ = checkPrg (I.Decl (Psi, D), (P, (F, T.id)))
        in
          F
        end
      | inferPrg (Psi, T.Let (D as T.PDec (_, F1, _, _), P1, P2)) =
        let
          val _ = checkPrg (Psi, (P1, (F1, T.id)))
          val F2 = inferPrg (I.Decl (Psi, D), P2)
        in
          F2
        end


    (* checkPrg (Psi, P, F) = ()

       Invariant:
       If   Psi  |- t1 : Psi1
       and  Psi1 |- P : F'
       and  Psi  |- F for     (F in normal form)
       and  P does not contain any P closures
       then checkPrg returns () iff F'[t1] == F[id]
    *)
    and checkPrg (Psi, (P, Ft)) = checkPrgW (Psi, (P, T.whnfFor Ft))
    and checkPrgW (_, (T.Unit, (T.True, _))) =
        let
          val _ = chatter 4 (fn () => "[true]")
        in
          ()
        end
      | checkPrgW (Psi, (T.Const lemma, (F, t))) =
          convFor (Psi, (inferLemma lemma, T.id), (F, t))
      | checkPrgW (Psi, (T.Var k, (F, t))) =
          (case T.ctxDec (Psi, k) of T.PDec (_, F', _, _) => convFor (Psi, (F', T.id), (F, t)))
      | checkPrgW (Psi, (T.Lam (D as T.PDec (x, F1, _, _), P), (T.All ((T.PDec (x', F1', _, _), _), F2), t))) =
        let
          val _ = chatter 4 (fn () => "[lam[p]")
            val _ = convFor (Psi, (F1, T.id), (F1', t))
          val _ = chatter 4 (fn () => "]")
        in
            checkPrg (I.Decl (Psi, D), (P, (F2, T.dot1 t)))
        end
      | checkPrgW (Psi, (T.Lam (T.UDec D, P), (T.All ((T.UDec D', _), F), t2))) =
        let
          val _ = chatter 4 (fn () => "[lam[u]")
          val _ = Conv.convDec ((D, I.id), (D', T.coerceSub t2))
          val _ = chatter 4 (fn () => "]")
        in
            checkPrg (I.Decl (Psi , T.UDec D), (P, (F, T.dot1 t2)))
        end
      | checkPrgW (Psi, (T.PairExp (M, P), (T.Ex((I.Dec(x, A), _), F2), t))) =
        let
          val _ = chatter 4 (fn () => "[pair [e]")
          val G = T.coerceCtx Psi
          val _ = TypeCheck.typeCheck(G, (M, I.EClo (A, T.coerceSub(t))))
          val _ = chatter 4 (fn () => "]")
        in
            checkPrg(Psi, (P, (F2, T.Dot (T.Exp M, t))))
        end
      | checkPrgW (Psi, (T.PairBlock (I.Bidx k, P), (T.Ex ((I.BDec (_, (cid, s)), _), F2), t))) =
        let
          val T.UDec (I.BDec(_, (cid', s'))) = T.ctxDec (Psi, k)
          val (G', _) = I.conDecBlock (I.sgnLookup cid)
          val _ = if (cid' <> cid) then raise Error ("Block label mismatch") else ()
          val _ = convSub (Psi, T.embedSub s', T.comp(T.embedSub(s), t), T.revCoerceCtx(G'))
        in
          checkPrg(Psi, (P, (F2, T.Dot(T.Block(I.Bidx k), t))))
        end
      | checkPrgW (Psi, (T.PairPrg (P1, P2), (T.And( F1, F2), t))) =
        let
          val _ = chatter 4 (fn () => "[and")
          val _ = checkPrg (Psi, (P1, (F1, t)))
          val _ = chatter 4 (fn () => "...")
          val _ = checkPrg (Psi, (P2, (F2, t)))
          val _ = chatter 4 (fn () => "]")
        in
          ()
        end
      | checkPrgW (Psi, (T.Case Omega, Ft)) =
          checkCases (Psi, (Omega, Ft))
      | checkPrgW (Psi, (T.Rec (D as T.PDec (x, F, _, _), P), (F', t))) =
        let
          val _ = chatter 4 (fn () => "[rec")
          val _ = convFor(Psi, (F, T.id), (F', t))
          val _ = chatter 4 (fn () => "]\n")
        in
            checkPrg (I.Decl(Psi, D), (P, (F', t)))
        end
      | checkPrgW (Psi, (T.Let (D as T.PDec(_, F1, _, _), P1, P2), (F2, t))) =
                                        (* Psi |- let xx :: F1 = P1 in P2 : F2' *)
                                        (* Psi |- t : Psi' *)
                                        (* Psi' |- F2 for *)
                                        (* Psi |- F2' = F2[t] *)
                                        (* Psi |- F1 :: for *)
                                        (* Psi |- P1 :: F1' *)
                                        (* Psi, D |- P2 :: (F2' [^]) *)
                                        (* Psi' |- F2' :: for *)
                                        (* Psi, D |- t o ^ :: Psi' *)
        let
          val _ = chatter 4 (fn () => "[let")
          val _ = checkPrg (Psi, (P1, (F1, T.id)))
                                        (* Psi |- F1 == F1' for *)
          val _ = chatter 4 (fn () => ".")
          val _ = checkPrg (I.Decl (Psi, D), (P2, (F2, T.comp (t, T.shift))))
          val _ = chatter 4 (fn () => "]\n")
        in
          ()
        end
      | checkPrgW (Psi, (T.New (P' as T.Lam (T.UDec (D as I.BDec (_, (cid, s))), P)), (F, t))) =
        let
          val _ = chatter 5 (fn () => "[new1...")
          val T.All ((T.UDec D'', _), F') = inferPrg (Psi, P')   (* D'' == D *)
          val _ = chatter 5 (fn () => "][new2...")
          val F'' = TA.raiseF (I.Decl (I.Null, D), (F', I.id))
        in
          (convFor (Psi, (F'', T.id), (F, t))
          ;chatter 5 (fn () => "]\n"))
        end
      | checkPrgW (Psi, (T.Redex (P1, S2), (F, t))) =
          let
            val F' = inferPrg (Psi, P1)
          in
           checkSpine (Psi, S2, (F', T.id), (F, t))
          end
      | checkPrgW (Psi, (T.Box (W, P), (T.World (W', F), t))) =
          checkPrgW (Psi, (P, (F, t)))
          (* don't forget to check if the worlds match up --cs Mon Apr 21 01:51:58 2003 *)

    and checkSpine (Psi, T.Nil, (F, t), (F', t')) =  convFor (Psi, (F, t), (F', t'))
      | checkSpine (Psi, T.AppExp (U, S), (T.All ((T.UDec (I.Dec (_, V)), _), F), t), (F', t')) =
        (TypeCheck.typeCheck (T.coerceCtx Psi, (U, I.EClo (V, T.coerceSub t)));
         checkSpine (Psi, S, (F, T.Dot (T.Exp U, t)), (F', t')))
      | checkSpine (Psi, T.AppPrg (P, S), (T.All ((T.PDec (_, F1, _, _) , _), F2), t),  (F', t')) =
        (checkPrgW (Psi, (P, (F1, t)));  checkSpine (Psi, S, (F2, T.Dot (T.Undef, t)), (F', t')))
      | checkSpine (Psi, T.AppExp (U, S), (T.FClo (F, t1) , t), (F', t')) =
          checkSpine (Psi, T.AppExp (U, S), (F, T.comp (t1 , t)), (F', t'))


    (* checkCases (Psi, (Omega, (F, t2))) = ()
       Invariant:
       and  Psi |- Omega : F'
       and  Psi |- F' for
       then checkCases returns () iff Psi |- F' == F [t2] formula
    *)
    and checkCases (Psi, (T.Cases nil, (F2, t2))) = ()
      | checkCases (Psi, (T.Cases ((Psi', t', P) :: Omega), (F2, t2))) =
        let
                                        (* Psi' |- t' :: Psi *)
          val _ = chatter 4 (fn () => "[case... ")
          val _ = chatter 4 (fn () => "sub... ")
          val _ = checkSub(Psi', t', Psi)
          val _ = chatter 4 (fn () => "prg... ")
          val t2' = T.comp(t2, t')
          val _ = checkCtx Psi
          val _ = checkCtx Psi'
          val _ = chatter 4 (fn () => "]")
          val _ = checkPrg (Psi', (P, (F2, t2')))
          val _ = chatter 4 (fn () => "]\n")

          val _ = checkCases (Psi, ((T.Cases Omega), (F2, t2)))
        in
          ()
        end

    and  inferLemma lemma =
        ( case (T.lemmaLookup lemma)
            of T.ForDec (_, F) => F
             | T.ValDec (_,_,F) => F)



    (* convFor (Psi, (F1, t1), (F2, t2)) = ()

       Invariant:
       If   Psi |- t1 :: Psi1
       and  Ps1 |- F1 for
    *)

    and convFor (Psi, Ft1, Ft2) = convForW (Psi, T.whnfFor Ft1, T.whnfFor Ft2)
    and convForW (_, (T.True, _), (T.True, _)) = ()
      | convForW (Psi,
                  (T.All ((D as T.UDec( I.Dec (_, A1)), _), F1), t1),
                  (T.All ((     T.UDec( I.Dec (_, A2)), _), F2), t2)) =
        let
          val G = T.coerceCtx (Psi)
          val s1 = T.coerceSub t1
          val s2 = T.coerceSub t2
          val _ = Conv.conv((A1, s1), (A2, s2))
          val _ = TypeCheck.typeCheck(G, (I.EClo (A1, s1), I.Uni I.Type))
          val _ = TypeCheck.typeCheck(G, (I.EClo (A2, s2), I.Uni I.Type))
          val D' = T.decSub (D, t1)
          val _ = convFor (I.Decl(Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.All ((D as T.UDec (I.BDec(_, (l1, s1))), _), F1), t1),
                  (T.All((T.UDec (I.BDec(_, (l2, s2))), _), F2), t2)) =
        let
          val _ = if l1 <> l2 then raise Error "Contextblock clash" else ()
          val (G', _) = I.conDecBlock (I.sgnLookup l1)
          val _ = convSub (Psi,
                           T.comp (T.embedSub s1, t1),
                           T.comp (T.embedSub s2, t2), T.embedCtx G')
          val D' = T.decSub (D, t1)
          val _ = convFor (I.Decl (Psi, D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.Ex ((D as I.Dec (_, A1), _), F1), t1),
                  (T.Ex ((     I.Dec (_, A2), _), F2), t2)) =
        let
          val G = T.coerceCtx (Psi)
          val s1 = T.coerceSub t1
          val s2 = T.coerceSub t2
          val _ = Conv.conv ((A1, s1), (A2, s2))
          val _ = TypeCheck.typeCheck (G, (I.EClo (A1, s1), I.Uni I.Type))
          val _ = TypeCheck.typeCheck (G, (I.EClo (A2, s2), I.Uni I.Type))
          val D' = I.decSub (D, s1)
          val _ = convFor (I.Decl(Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.Ex ((D as I.BDec(name, (l1, s1)), _), F1), t1),
                  (T.Ex ((     I.BDec(_,    (l2, s2)), _), F2), t2)) =
        let
          val _ = if l1 <> l2 then raise Error "Contextblock clash" else ()
          val (G', _) = I.conDecBlock (I.sgnLookup l1)
          val s1 = T.coerceSub t1
          val _ = convSub (Psi,
                           T.comp (T.embedSub s1, t1),
                           T.comp (T.embedSub s2, t2), T.embedCtx G')
          val D' = I.decSub (D, s1)
          val _ = convFor (I.Decl(Psi, T.UDec D'), (F1, T.dot1 t1), (F2, T.dot1 t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.And(F1, F1'), t1),
                  (T.And(F2, F2'), t2)) =
        let
          val _ = convFor (Psi, (F1,  t1), (F2,  t2))
          val _ = convFor (Psi, (F1', t1), (F2', t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.All((D as T.PDec(_, F1, _, _), _), F1'), t1),
                  (T.All((     T.PDec(_, F2, _, _), _), F2'), t2)) =
        let
          val _ = convFor (Psi, (F1, t1), (F2, t2))
          val D' = T.decSub (D, t1)
          val _ = convFor (I.Decl (Psi, D'), (F1', T.dot1 t1), (F2', T.dot1 t2))
        in
          ()
        end
      | convForW (Psi,
                  (T.World (W1, F1), t1),
                  (T.World (W2, F2), t2)) =
        let
          val _ = convFor (Psi, (F1, t1), (F2, t2))
          (* also check that both worlds are equal -- cs Mon Apr 21 01:28:01 2003 *)
        in
          ()
        end

      | convForW _ = raise Error "Typecheck error"

    and convSub(G, T.Shift k1, T.Shift k2, G') = if k1=k2 then () else raise Error "Sub not equivalent"
      | convSub(G, T.Shift k, s2 as T.Dot _, G') = convSub(G, T.Dot(T.Idx(k+1), T.Shift(k+1)), s2, G')
      | convSub(G, s1 as T.Dot _, T.Shift k, G') = convSub(G, s1, T.Dot(T.Idx(k+1), T.Shift(k+1)), G')
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', _)) =
        if k1=k2 (* For s1==s2, the variables in s1 and s2 must refer to the same cell in the context -- Yu Liao *)
        then convSub(G, s1, s2, G')
        else raise Error "Sub not equivalent"
      | convSub(G, T.Dot(T.Exp M1, s1), T.Dot(T.Exp M2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
        let
            val _ = TypeCheck.checkConv (M1, M2) (* checkConv doesn't need context G?? -- Yu Liao *)
            val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M1, A))
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Block (I.Bidx v1), s1), T.Dot(T.Block(I.Bidx v2), s2), I.Decl(G', T.UDec (I.BDec (_, (l,s)))))=
        let
            val T.UDec (I.BDec(_, (l1, s11)))= T.ctxDec(G, v1)
            val T.UDec (I.BDec(_, (l2, s22)))= T.ctxDec(G, v2)
            val _ = if l1 = l2 then () else raise Error "Sub not equivalent"
            val _ = if l1 = l then () else raise Error "Sub not equivalent"
            val (G'', _) = I.conDecBlock (I.sgnLookup l)
            val _ = convSub (G, T.embedSub s11, T.embedSub s22, T.revCoerceCtx(G''))
            val _ = convSub (G, T.embedSub s11, T.embedSub s, T.revCoerceCtx(G''))
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Prg P1, s1), T.Dot(T.Prg P2, s2), I.Decl(G', T.PDec(_, F, _, _))) =
        let
            val _ = isValue P1
            val _ = isValue P2
            val _ = convValue (G, P1, P2, F)
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Exp M2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
        let
            val _ = TypeCheck.checkConv (I.Root(I.BVar k1, I.Nil), M2)
            val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M2, A))
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Exp M1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', T.UDec(I.Dec(_, A)))) =
        let
            val _ = TypeCheck.checkConv (M1, I.Root(I.BVar k2, I.Nil))
            val _ = TypeCheck.typeCheck (T.coerceCtx(G), (M1, A))
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Idx k1, s1), T.Dot(T.Prg P2, s2), I.Decl(G', T.PDec(_, F, _, _))) =
        let
            val _ = isValue P2
            val _ = convValue (G, T.Var k1, P2, F)
        in
            convSub(G, s1, s2, G')
        end
      | convSub(G, T.Dot(T.Prg P1, s1), T.Dot(T.Idx k2, s2), I.Decl(G', T.PDec(_, F, _, _))) =
        let
            val _ = isValue P1
            val _ = convValue (G, P1, T.Var k2, F)
        in
            convSub(G, s1, s2, G')
        end

    and convValue (G, P1, P2, F) = ()
    and checkFor (Psi, (T.True, _)) = ()
      | checkFor (Psi, (T.All ((D as T.PDec (_ ,F1, _, _), _), F2), t)) =
          (checkFor (Psi, (F1, t)); checkFor (I.Decl (Psi, D), (F2, T.dot1 t)))
      | checkFor (Psi, (T.All ((D' as T.UDec D, _), F), t)) =
          (TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
           checkFor (I.Decl (Psi, D'), (F, T.dot1 t)))
      | checkFor (Psi, (T.Ex  ((D, _), F), t)) =
          (TypeCheck.checkDec (T.coerceCtx Psi, (D, T.coerceSub t));
           checkFor (I.Decl (Psi, T.UDec D), (F, T.dot1 t)))
      | checkFor (Psi, (T.And (F1, F2), t)) =
          (checkFor (Psi, (F1, t)); checkFor (Psi, (F2, t)))
      | checkFor (Psi, (T.FClo (F, t'), t)) =
          checkFor (Psi, (F, T.comp (t', t)))
      | checkFor (Psi, (T.World (W, F), t)) =
          checkFor (Psi, (F, t))


    and checkCtx (I.Null) = ()
      | checkCtx (I.Decl (Psi, T.UDec D)) =
          (checkCtx (Psi);
           TypeCheck.checkDec (T.coerceCtx Psi, (D, I.id)))
      | checkCtx (I.Decl (Psi, T.PDec (_, F, _, _))) =
          (checkCtx (Psi);
           checkFor (Psi, (F, T.id)))


    (* checkSub (Psi, t, Psi') = ()

       Invariant
       If Psi |- t: Psi' then checkSub terminates with ()
       otherwise exception Error is raised
    *)

    and checkSub (I.Null, T.Shift 0, I.Null) = ()
      | checkSub (I.Decl (G, D), T.Shift k, I.Null) =
        if k > 0
        then checkSub (G, T.Shift (k-1), I.Null)
        else raise Error "Sub is not well typed!"
      | checkSub (G, T.Shift k, G') = checkSub (G, T.Dot (T.Idx (k+1), T.Shift (k+1)), G')
      | checkSub (G, T.Dot (T.Idx k, s'), I.Decl (G', (T.UDec (I.Dec (_, A))))) =
        let
            val _ = checkSub (G, s', G')
            val T.UDec (I.Dec (_, A')) = T.ctxDec (G, k)
        in
            if Conv.conv ((A', I.id), (A, T.coerceSub(s'))) then ()
            else raise Error "Sub isn't well typed!"
        end
      | checkSub (G, T.Dot (T.Idx k, s'), I.Decl (G', T.UDec (I.BDec(l, (_, s))))) =
        let
            val _ = checkSub (G, s', G')
            val T.UDec (I.BDec(l1, (_, s1))) = T.ctxDec (G, k)
        in
            if (l<> l1) then raise Error "Sub isn't well typed!"
            else
                if Conv.convSub (I.comp (s, T.coerceSub(s')), s1)
                then ()
                else raise Error "Sub isn't well typed!"
        end
      | checkSub (G, T.Dot (T.Idx k, s), I.Decl (G', T.PDec(_, F', _, _))) =
        let
            val _ = checkSub (G, s, G')
            val T.PDec(_, F1, _, _) = T.ctxDec (G, k)
        in
            convFor (G, (F1, T.id), (F', s))
        end
      | checkSub (G, T.Dot (T.Exp M, s), I.Decl(G', T.UDec (I.Dec (_, A)))) =
        let
            val _ = checkSub (G, s, G')
        in
            TypeCheck.typeCheck (T.coerceCtx G, (M, I.EClo(A, T.coerceSub(s))))
        end
      | checkSub (Psi, T.Dot (T.Prg P, t), I.Decl(Psi', T.PDec(_, F', _, _))) =
        let
          val _ = chatter 4 (fn () => "$")
          val _ = checkSub (Psi, t, Psi')
          val _ = isValue P
        in
            checkPrg (Psi, (P, (F', t)))
        end
      | checkSub (Psi, T.Dot (T.Block B, t), I.Decl(Psi', T.UDec (I.BDec(l2, (c, s2))))) =
        let
          val _ = chatter 4 (fn () => "$")
          val _ = checkSub (Psi, t, Psi')
                                        (* Psi |- t : Psi' *)
                                        (* Psi' |- s2 : SOME variables of c *)
          val (G, L) = I.constBlock c
                                        (* Psi |- s2 : G *)
          val _ = TypeCheck.typeCheckSub (T.coerceCtx Psi', s2, G)
        in
            checkBlock (Psi, (B, (c, I.comp (s2, T.coerceSub t))))
        end
      | checkSub (Psi, T.Dot _, I.Null) = raise Error "Sub is not well typed"


    and checkBlock (Psi, (I.Bidx v, (c2, s2))) =
        let
          val T.UDec (I.BDec(l1, (c1, s1))) = T.ctxDec (Psi, v)
        in
          if (c1 <> c2) then raise Error "Sub isn't well typed!"
          else if Conv.convSub (s2, s1)  then ()
               else raise Error "Sub isn't well typed!"
        end
      | checkBlock (Psi, (I.Inst UL, (c2, s2))) =
        let
          val (G, L) = I.constBlock c2
                                        (* Psi |- s2 : G *)
          val _ = TypeCheck.typeCheckSub (T.coerceCtx Psi, s2, G)
        in
          checkInst (Psi, UL, (1, L, s2))
        end

   (* Invariant:

      If   Psi |- s2 : Psi'    Psi' |-  Bn ... Bm
      and  Psi |- s : [cn :An ... cm:Am]
      and  Ai == Bi n<= i<=m
      then checkInst returns () otherwise an exception is raised.
   *)
   and checkInst (Psi, nil, (_, nil, _)) = ()
     | checkInst (Psi, U :: UL, (n, D :: L, s2)) =
       let
         val G = T.coerceCtx Psi
         val I.Dec (_ ,V) = I.decSub (D, s2)
         val _ = TypeCheck.typeCheck (G, (U, V))
       in
         checkInst (Psi, UL, (n+1, L, I.dot1 s2))
       end



    and isValue (T.Var _) = ()
      | isValue (T.PClo (T.Lam _, _)) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Rec _) = ()
      | isValue (T.Const lemma) =
        ( case (T.lemmaLookup lemma) of
              T.ForDec _ => raise Error "Lemma isn't a value"
            | T.ValDec(_,P,_) => isValue P )
      | isValue _ = raise Error "P isn't Value!"



(*  remove later!
    and isValue (T.Lam _) = ()
      | isValue (T.PairExp (M, P)) = isValue P
      | isValue (T.PairBlock _ ) = ()
      | isValue (T.PairPrg (P1, P2)) = (isValue P1; isValue P2)
      | isValue T.Unit = ()
      | isValue (T.Root ((T.Const lemma), T.Nil)) = (* could lemma be a VALUE? -- Yu Liao *)
        ( case (T.lemmaLookup lemma) of
              T.ForDec _ => raise Error "Lemma isn't a value"
            | T.ValDec(_,P,_) => isValue P )

      | isValue (T.Root ((T.Var k), T.Nil)) = ()
      | isValue (T.Rec _) = ()

      (* ABP 1/23/03 *)
      | isValue (T.EVar _) = raise Error "It is an EVar"

      | isValue _ = raise Error "P isn't Value!"
*)

    fun check (Psi, (P, F)) = checkPrg (Psi, (P, (F, T.id)))



  in
  val checkPrg = fn (Psi, (P, F)) => checkPrg (Psi, (P, (F, T.id)))
  val checkSub = checkSub
  val checkFor = fn (Psi, F) => checkFor (Psi, (F, T.id))
  val checkCtx = checkCtx
  end
end
