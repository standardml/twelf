 (* Type checking for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor FunTypeCheck ((*! structure FunSyn' : FUNSYN !*)
                      structure StateSyn' : STATESYN
                      (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                      structure Abstract : ABSTRACT
                      (*! sharing Abstract.IntSyn = FunSyn'.IntSyn !*)
                      structure TypeCheck : TYPECHECK
                      (*! sharing TypeCheck.IntSyn = FunSyn'.IntSyn !*)
                      structure Conv : CONV
                      (*! sharing Conv.IntSyn = FunSyn'.IntSyn !*)
                      structure Whnf : WHNF
                      (*! sharing Whnf.IntSyn = FunSyn'.IntSyn !*)
                      structure Print : PRINT
                      (*! sharing Print.IntSyn = FunSyn'.IntSyn !*)
                      structure Subordinate : SUBORDINATE
                      (*! sharing Subordinate.IntSyn = FunSyn'.IntSyn !*)
                      structure Weaken : WEAKEN
                      (*! sharing Weaken.IntSyn = FunSyn'.IntSyn   !*)
                      structure FunPrint : FUNPRINT
                      (*! sharing FunPrint.FunSyn = FunSyn' !*)
                          ) : FUNTYPECHECK=
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure F = FunSyn
    structure S = StateSyn

    (* conv ((G, s), (G', s')) = B

       Invariant:
       B iff G [s]  == G' [s']
       Might migrate in to conv module  --cs
    *)
    fun conv (Gs, Gs') =
      let
        exception Conv
        fun conv ((I.Null, s), (I.Null, s')) = (s, s')
          | conv ((I.Decl (G, I.Dec (_, V)), s),
                  (I.Decl (G', I.Dec (_, V')), s')) =
            let
              val (s1, s1') = conv ((G, s), (G', s'))
              val ps as (s2, s2') = (I.dot1 s1, I.dot1 s1')
            in
              if Conv.conv ((V, s1), (V', s1')) then ps
              else raise Conv
            end
          | conv _ = raise Conv
      in
        (conv (Gs, Gs'); true) handle Conv => false
      end



    (* extend (G, L) = G'

       Invariant:
       If   G : 'a ctx
       and  L : 'a list
       then G' = G, L : 'a ctx
    *)
    fun extend (G, nil) = G
      | extend (G, D :: L) = extend (I.Decl (G, D), L)


    (* validBlock (Psi, k, (l : G)) = ()

       Invariant:
       If   |- Psi ctx
       and  |- k is a debruijn index (for LF context)
       and  |- l label
       and  |- G LFctx
       then validBlock terminates with ()
       iff  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  l = l'
       and  Psi(k) = x1
       and  G == x1:A1 .. xn:An
    *)

    fun validBlock (Psi, k, (l, G)) =
      let
        fun skipBlock (I.Null, k) = k
          | skipBlock (I.Decl (G', _), k) = skipBlock (G', k-1)

        fun validBlock' (I.Decl (Psi, F.Block (F.CtxBlock (l', G'))), 0) =
              if (l' = l) andalso conv ((G, I.id), (G', I.id)) then ()
              else raise Error "Typecheck Error: Not a valid block"
          | validBlock' (I.Decl (Psi, F.Prim _), 0) =
              raise Error "Typecheck Error: Not a valid block"
          | validBlock' (I.Null, k) =
              raise Error "Typecheck Error: Not a valid block"
          | validBlock' (I.Decl (Psi, F.Block (F.CtxBlock (l', G'))), k) =
              validBlock' (Psi, skipBlock (G', k))
          | validBlock' (I.Decl (Psi, F.Prim (D)), k) =
              validBlock' (Psi, k-1)

      in
        validBlock' (Psi, k)
      end

    (* raiseSub (l:G, Psi') = s'

       Invariant:
       If   |- Psi ctx
       and  Psi |- l:G ctx
       and  Psi, l:G |- Psi' ctx
       then Psi, {G} Psi', l:G|- s' : Psi, l:G, Psi'
    *)
    fun raiseSub (G, Psi') =
      let
        val n = I.ctxLength G
        val m = I.ctxLength Psi'

        fun args (0, a, S) = S
          | args (n', a, S) =
            let
              val I.Dec (_, V) = I.ctxDec (G, n')
            in
              if Subordinate.belowEq (I.targetFam V, a)
                then args (n'-1, a, I.App (I.Root (I.BVar n', I.Nil), S))
              else args (n'-1, a, S)
            end

        fun term m' =
            let
              val I.Dec (_, V) = I.ctxDec (Psi', m')
            in
              I.Exp (I.Root (I.BVar (n+m'), args (n, I.targetFam (V), I.Nil)))
            end

        fun raiseSub'' (0, s) = s
          | raiseSub'' (m', s) = raiseSub'' (m'-1, I.Dot (term m', s))

        fun raiseSub' (0, s) = raiseSub'' (m, s)
          | raiseSub' (n', s) = raiseSub' (n'-1, I.Dot (I.Idx n', s))

      in
        raiseSub' (n, I.Shift (n+m))
      end

    (* raiseType (l:G, L) = L'

       Invariant:
       L contains no parameter block declarations
       Each x:A in L is mapped xto  x:{G}A in L'
       L' preserves the order of L
    *)

    fun raiseType (F.CtxBlock (l, G), Psi') =
      let
        fun raiseType'' (I.Null, Vn, a) = Vn
          | raiseType'' (I.Decl (G', D as I.Dec (_, V')), Vn, a) =
            if Subordinate.belowEq (I.targetFam V', a)
              then raiseType'' (G', Abstract.piDepend ((D, I.Maybe), Vn), a)
            else raiseType'' (G', Weaken.strengthenExp (Vn, I.shift), a)
        fun raiseType' (Psi1, nil) = nil
          | raiseType' (Psi1, F.Prim (D as I.Dec (x, V)) :: Psi1') =
            let
              val s = raiseSub (G, Psi1)
              val Vn = Whnf.normalize (V, s)
              val a = I.targetFam Vn
              val D' = I.Dec (x, raiseType'' (G, Vn, a))
            in
              F.Prim (D') :: (raiseType'(I.Decl (Psi1, D),  Psi1'))
            end
          (* no case of F.Block by invariant *)
      in
        raiseType' (I.Null, Psi')
      end


    (* raiseM (B, L) = L'

       Invariant
       Each xx in F in L is mapped to xx in PI B. F in L'
       L' preserves the order of L
    *)
    fun raiseM (B, nil) = nil
      | raiseM (B, F.MDec (xx, F) :: L) =
          F.MDec (xx, F.All (F.Block B, F)) :: raiseM (B, L)

    (* psub (k, Phi, s) = s'

       Invariant:
       If   |- Phi ctx
       and  |- Psi ctx
       and  Psi = Psi1, l': (x1:A1 .. xn:An), Psi2
       and  Psi (k) = x1
       and  | Phi | = n
       and  s = k-i ... k. id   for i <=n
       then s' = k-n . ... k . id
    *)

    fun psub (k, I.Null, s) = s
      | psub (k, I.Decl (G, _), s) =
          psub (k-1, G, I.Dot (I.Idx k, s))


    fun deltaSub (I.Null, s) = I.Null
      | deltaSub (I.Decl (Delta, DD), s) =
          I.Decl (deltaSub (Delta, s), F.mdecSub (DD, s))

    fun shift Delta = deltaSub (Delta, I.shift)

    fun shifts (I.Null, Delta) = Delta
      | shifts (I.Decl (G, _), Delta) =
          shifts (G, shift Delta)

    fun shiftBlock (F.CtxBlock (_, G), Delta) =
      shifts (G, Delta)

    fun shiftSub (I.Null, s) = s
      | shiftSub (I.Decl (G, _), s) = shiftSub (G, I.comp (I.shift, s))

    fun shiftSubBlock (F.CtxBlock (_, G), s) =
      shiftSub (G, s)

    (* check (Psi, Delta, P, (F, s)) = ()

       Invariant:
       If   Psi'' |- F formula
       and  Psi |- s : Psi''
       and  Psi |- Delta mctx
        returns () if there exists a F',
              s.t. Psi, Delta |- P  : F'
              and  Psi |- F' = F[s] formula
       otherwise Error is raised
    *)
    fun check (Psi, Delta, F.Unit, (F.True, _)) = ()
      | check (Psi, Delta, F.Rec (DD, P), F) =
          (check (Psi, I.Decl (Delta, DD), P, F))
      | check (Psi, Delta, F.Lam (LD as F.Prim (I.Dec (_, V)), P),
               (F.All (F.Prim (I.Dec (_, V')), F'), s')) =
        if (Conv.conv ((V, I.id), (V', s'))) then
          check (I.Decl (Psi, LD), shift Delta,
                 P, (F', I.dot1 s'))
         else raise Error "Typecheck Error: Primitive Abstraction"
      | check (Psi, Delta, F.Lam (LD as F.Block (B as F.CtxBlock (l, G)), P),
               (F.All (F.Block (F.CtxBlock (l', G')), F'), s')) =
        (if (l = l' andalso conv ((G, I.id), (G', s'))) then
           check (I.Decl (Psi, LD), shiftBlock (B, Delta),
                  P,
                  (F', F.dot1n (G, s')))
         else raise Error "Typecheck Error: Block Abstraction")
      | check (Psi, Delta, F.Inx (M, P), (F.Ex (I.Dec (_, V'), F'), s')) =
          (TypeCheck.typeCheck (F.makectx Psi, (M, (I.EClo (V', s'))));
           check (Psi, Delta, P, (F', I.Dot (I.Exp (M), s'))))
      | check (Psi, Delta, F.Case (F.Opts O), (F', s')) =
          checkOpts (Psi, Delta, O, (F', s'))
      | check (Psi, Delta, F.Pair (P1, P2), (F.And (F1', F2'), s')) =
          (check(Psi, Delta, P1, (F1', s'));
           check(Psi, Delta, P2, (F2', s')))
      | check (Psi, Delta, F.Let (Ds, P), (F', s')) =
        let
          val (Psi', Delta', s'') = assume (Psi, Delta, Ds)
        in
          check (extend (Psi, Psi'), extend (Delta, Delta'), P, (F', I.comp (s', s'')))
        end
      | check _ = raise Error "Typecheck Error: Term not well-typed"

    and infer (Delta, kk) = (I.ctxLookup (Delta, kk), I.id)

    (* assume (Psi, Delta, Ds) = (Psi', Delta', s')

       Invariant:
       If   |- Psi context
       and  Psi |- Delta assumptions
       and  Psi, Delta |- Decs declarations
       then |- Psi, Psi' context
       and  Psi, Psi' |- Delta, Delta' assumptions
       and  Psi, Psi' |- s' = ^|Psi'| : Psi
    *)

    and assume (Psi, Delta, F.Empty) = (nil, nil, I.id)
      | assume (Psi, Delta, F.Split (kk, Ds)) =
        (case infer (Delta, kk) of
          (F.MDec (name, F.Ex (D, F)), s) =>
            let
              val LD = F.Prim (I.decSub (D, s))
              val DD = F.MDec (name, F.forSub (F, I.dot1 s))
              val (Psi', Delta', s') = assume (I.Decl (Psi, LD),
                                               I.Decl (shift Delta, DD), Ds)
            in
              (LD :: Psi', F.mdecSub (DD, s') :: Delta', I.comp (I.shift, s'))
            end
        | _ => raise Error "Typecheck Error: Declaration")
      | assume (Psi, Delta, F.New (B, Ds)) =
        let
          (* check B valid context block       <-------------- omission *)
          val _ = TypeCheck.typeCheck (F.makectx (I.Decl (Psi, F.Block B)), (I.Uni I.Type, I.Uni I.Kind))
          val (Psi', Delta', s') =  assume (I.Decl (Psi, F.Block B),
                                            shiftBlock (B, Delta), Ds)
        in
          (raiseType (B, Psi'), raiseM (B, Delta'),  s')
        end
      | assume (Psi, Delta, F.App ((kk, U), Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.All (F.Prim (I.Dec (_, V)), F)), s) =>
             let
               val _ = TypeCheck.typeCheck (F.makectx Psi, (U, I.EClo (V, s)))
                 handle TypeCheck.Error msg =>
                   raise Error (msg ^  " " ^
                                Print.expToString (F.makectx Psi, U) ^
                                " has type " ^
                                Print.expToString (F.makectx Psi,
                                                   TypeCheck.infer' (F.makectx Psi, U)) ^
                                " expected " ^
                                Print.expToString (F.makectx Psi, I.EClo (V, s)))
               val DD = F.MDec (name, F.forSub (F, I.Dot (I.Exp (U), s)))
               val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | (F.MDec (name, F), s) =>
             raise Error ("Typecheck Error: Declaration App" ^
                             (FunPrint.forToString (I.Null, F) ["x"])))
      | assume (Psi, Delta, F.PApp ((kk, k), Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.All (F.Block (F.CtxBlock (l, G)), F)), s) =>
             let
               val _ = validBlock (Psi, k, (l, G))
               val DD = F.MDec (name, F.forSub (F, psub(k, G, s)))
               val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration PApp")
      | assume (Psi, Delta, F.Left (kk, Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.And (F1, F2)), s) =>
             let
               val DD = F.MDec (name, F.forSub (F1, s))
               val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration Left")
      | assume (Psi, Delta, F.Right (kk, Ds)) =
        (case infer (Delta, kk) of
           (F.MDec (name, F.And (F1, F2)), s) =>
             let
               val DD = F.MDec (name, F.forSub (F2, s))
               val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds)
             in
               (Psi', F.mdecSub (DD, s') :: Delta', s')
             end
         | _ => raise Error "Typecheck Error: Declaration Left")
      | assume (Psi, Delta, F.Lemma (cc, Ds)) =
        let
          val F.LemmaDec (names, _, F) = F.lemmaLookup cc
          val name = foldr op^ "" names
          val DD = F.MDec (SOME name, F)
          val (Psi', Delta', s') = assume (Psi, I.Decl (Delta, DD), Ds)
        in
          (Psi', F.mdecSub (DD, s') :: Delta', s')
        end


    (* checkSub (Psi1, s, Psi2) = ()

       Invariant:
       The function terminates
       iff  Psi1 |- s : Psi2
    *)
    and checkSub (I.Null, I.Shift 0, I.Null) = ()
      | checkSub (I.Decl (Psi, F.Prim D), I.Shift k, I.Null) =
        if k>0 then checkSub (Psi, I.Shift (k-1), I.Null)
        else raise Error "Substitution not well-typed"
      | checkSub (I.Decl (Psi, F.Block (F.CtxBlock (_, G))), I.Shift k, I.Null) =
        let
          val g = I.ctxLength G
        in
          if k>=g then checkSub (Psi, I.Shift (k-g), I.Null)
          else raise Error "Substitution not well-typed"
        end
      | checkSub (Psi', I.Shift k, Psi) =
          checkSub (Psi', I.Dot (I.Idx (k+1), I.Shift (k+1)), Psi)
      | checkSub (Psi', I.Dot (I.Idx k, s'), I.Decl (Psi, F.Prim (I.Dec (_, V2)))) =
        let
          val G' = F.makectx Psi'
          val I.Dec (_, V1) = I.ctxDec (G', k)
        in
          if Conv.conv ((V1, I.id), (V2, s')) then checkSub (Psi', s', Psi)
          else raise Error ("Substitution not well-typed \n  found: " ^
                            Print.expToString (G', V1) ^ "\n  expected: " ^
                            Print.expToString (G', I.EClo (V2, s')))
        end
      | checkSub (Psi', I.Dot (I.Exp (U), s'), I.Decl (Psi, F.Prim (I.Dec (_, V2)))) =
        let
          val G' = F.makectx Psi'
          val _ = TypeCheck.typeCheck (G', (U, I.EClo (V2, s')))
        in
          checkSub (Psi', s', Psi)
        end
      | checkSub (Psi', s as I.Dot (I.Idx k, _), I.Decl (Psi, F.Block (F.CtxBlock (l1, G)))) =
        let
          val (F.Block (F.CtxBlock (l2, G')), w) = F.lfctxLFDec (Psi', k)
          (* check that l1 = l2     <----------------------- omission *)

          (* checkSub' ((G', w), s, G, m) = ()
          *)

          fun checkSub' ((I.Null, w1), s1, I.Null, _) = s1
            | checkSub' ((I.Decl (G', I.Dec (_, V')), w1), I.Dot (I.Idx k', s1),
                         I.Decl (G, I.Dec (_, V)), m) =
              if k' = m then
                if Conv.conv ((V', w1), (V, s1)) then
                  checkSub' ((G', I.comp (w1, I.shift)), s1, G, m + 1)
                else raise Error "ContextBlock assignment not well-typed"
              else raise Error "ContextBlock assignment out of order"
        in
          checkSub (Psi', checkSub' ((G', w), s, G, k), Psi)
        end


    (* checkOpts (Psi, Delta, (O, s) *)

    and checkOpts (Psi, Delta, nil, _) = ()
      | checkOpts (Psi, Delta, (Psi', t, P)::O, (F', s')) =
          (checkSub (Psi', t, Psi);
           check (Psi', deltaSub (Delta, t), P, (F', I.comp (s', t)));
           (* [Psi' strict in  t] <------------------------- omission*)
           checkOpts(Psi, Delta, O, (F', s')))

    fun checkRec (P, T) =
      check (I.Null, I.Null, P, (T, I.id))


    fun isFor (G, F.All (F.Prim D, F)) =
          ((TypeCheck.checkDec (G, (D, I.id));
            isFor (I.Decl (G, D), F))
           handle TypeCheck.Error msg => raise Error msg)
      | isFor (G, F.All (F.Block (F.CtxBlock (_, G1)), F)) =
          isForBlock (G, F.ctxToList G1, F)
      | isFor (G, F.Ex (D, F)) =
          ((TypeCheck.checkDec (G, (D, I.id));
            isFor (I.Decl (G, D), F))
           handle TypeCheck.Error msg => raise Error msg)
      | isFor (G, F.True) = ()
      | isFor (G, F.And (F1, F2)) =
          (isFor (G, F1); isFor (G, F2))

    and isForBlock (G, nil, F) = isFor (G, F)
      | isForBlock (G, D :: G1, F) = isForBlock (I.Decl (G, D), G1, F)





    fun checkTags' (V, F.Ex _) = ()
      | checkTags' (I.Pi (_, V), F.All (_, F)) =
          checkTags' (V, F)
      | checkTags' _ = raise Domain

    fun checkTags (I.Null, I.Null) = ()
      | checkTags (I.Decl (G, I.Dec (_, V)), I.Decl (B, T)) =
        (checkTags (G, B);
         case T
           of S.Lemma (_) =>  ()
            | _ => ())


    (* isState (S) = ()

       Invariant:

       Side effect:
       If it doesn't hold that |- S state, then exception Error is raised

       Remark: Function is only partially implemented
    *)
    fun isState (S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        (TypeCheck.typeCheckCtx G;
         checkTags (G, B);
         if (not (Abstract.closedCtx G)) then raise Error "State context not closed!" else ();
         map (fn (n', F') => (isFor (G, F')
(* ;          TextIO.print ("Checked: " ^ (FunPrint.Formatter.makestring_fmt (FunPrint.formatForBare (G, F'))) ^ "\n") *) )) H;
         (* n' is not checked for consistency   --cs *)
         isFor (G, F))



  in
    val isFor = isFor
    val check = checkRec
    val checkSub = checkSub
    val isState = isState
  end
end (* Signature FUNTYPECHECK *)
