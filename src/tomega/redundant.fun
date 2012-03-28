(* Redundancy remover (factoring) *)
(* Author: Adam Poswolsky (ABP) *)

functor Redundant (structure Opsem : OPSEM) : REDUNDANT  =
  struct
    exception Error of string

    (*
     convert:  Tomega.Prg -> Tomega.Prg
     Attempts to eliminate *redundant* cases.
     *)
    structure T = Tomega
    structure I = IntSyn

    fun optionRefEqual (r1, r2, func) =
      if (r1 = r2) then
        true
      else
        (case (r1, r2)
           of (ref NONE, ref NONE) => true
           |  (ref (SOME (P1)), ref (SOME (P2))) => func(P1, P2)
           |  _ => false
        )

    fun convert (T.Lam (D, P)) = T.Lam (D, convert P)
      | convert (T.New P) = T.New (convert P)
      | convert (T.Choose P) = T.Choose (convert P)
      | convert (T.PairExp (M, P)) = T.PairExp (M, convert P)
      | convert (T.PairBlock (rho, P)) = T.PairBlock (rho, convert P)
      | convert (T.PairPrg (P1, P2)) = T.PairPrg (convert P1, convert P2)
      | convert (T.Unit) = T.Unit
      | convert (T.Var x) = T.Var x
      | convert (T.Const x) = T.Const x
      | convert (T.Redex (P, S)) = T.Redex (convert P, convertSpine S)
      | convert (T.Rec (D, P)) = T.Rec (D, convert P)
      | convert (T.Case (T.Cases O)) = T.Case (T.Cases (convertCases O))
      | convert (T.Let (D,P1,P2)) = T.Let (D, convert P1, convert P2)
    (* No EVARs will occur
      | convert (T.PClo (P,t)) = raise Error "No PClo should exist" (* T.PClo (convert P, t) *)
      | convert (T.EVar (D, P as ref NONE, F)) = T.EVar (D, P, F)
      | convert (T.EVar (D, ref (SOME P), F)) = convert P (* some opsem here *)
    *)


    and convertSpine (T.Nil) = T.Nil
      | convertSpine (T.AppExp (I, S)) = (T.AppExp (I, convertSpine S))
      | convertSpine (T.AppBlock (I, S)) = (T.AppBlock (I, convertSpine S))
      | convertSpine (T.AppPrg (P, S)) = (T.AppPrg (convert P, convertSpine S))
      | convertSpine (T.SClo (S, t)) = raise Error "SClo should not exist"
                             (* (T.SClo (convertSpine S, t)) *)


    and expEqual (E1, E2) = Conv.conv ( (E1, I.id), (E2, I.id) )


    and IsubEqual (sub1, sub2) = Conv.convSub(sub1, sub2) (* Note that it doesn't handle blocks *)


    and blockEqual (I.Bidx x, I.Bidx x') = (x=x')
      (* Should not occur -- ap 2/18/03 *)
      | blockEqual (I.LVar (r, sub1, (cid, sub2)), I.LVar (r', sub1', (cid', sub2'))) =
          optionRefEqual(r,r',blockEqual) andalso IsubEqual(sub1, sub1') andalso (cid = cid') andalso IsubEqual(sub1', sub2')
      | blockEqual _ = false


    and decEqual ( T.UDec (D1), (T.UDec (D2), t2) ) = Conv.convDec ((D1, I.id),(D2, T.coerceSub(t2)))
      | decEqual ( T.PDec (_, F1, _, _), (T.PDec (_, F2, _, _), t2) ) = T.convFor ((F1, T.id), (F2, t2))
      | decEqual _ = false

    and caseEqual (((Psi1, t1, P1)::O1), (((Psi2, t2, P2)::O2), tAfter)) =
            (* Recall that we (Psi2, t2, P2)[tAfter] = (Psi2, (tAfterInv \circ t2), P2) *)
            let
              val t2' = T.comp(T.invertSub(tAfter),t2)
              (* Note:  (Psi1 |- t1: Psi0) *)
              val t = Opsem.createVarSub(Psi1, Psi2) (* Psi1 |- t: Psi2 *)
              val t' = T.comp(t2', t) (* Psi1 |- t' : Psi_0 *)
              val doMatch = (Opsem.matchSub (Psi1, t1, t') ; true)
                handle NoMatch => false
            in
              if (doMatch) then
                let
                  val newT = T.normalizeSub t
                  val stillMatch = IsSubRenamingOnly(newT)
                in
                  (stillMatch andalso prgEqual(P1, (P2, cleanSub(newT))))
                end
              else
                false
            end


      | caseEqual (nil, (nil, t2)) = true
      | caseEqual _ = false

    and spineEqual ( (T.Nil), (T.Nil, t2) ) = true
      | spineEqual ( (T.AppExp(E1,S1)), (T.AppExp(E2,S2), t2) ) = (Conv.conv( (E1,I.id), (E2, T.coerceSub(t2)) ) andalso spineEqual(S1,(S2,t2)))
      | spineEqual ( (T.AppBlock (B1,S1)), (T.AppBlock(B2,S2), t2) ) = (blockEqual( B1, I.blockSub (B2, T.coerceSub t2)) andalso spineEqual(S1,(S2,t2)))

      | spineEqual ( (T.AppPrg (P1,S1)), (T.AppPrg(P2,S2), t2) ) = (prgEqual(P1, (P2, t2)) andalso spineEqual(S1, (S2,t2)))

      | spineEqual ( T.SClo(S,t1), (T.SClo(s,t2a), t2) ) =
(* there are no SClo created in converter *) raise Error "SClo should not exist!"

      | spineEqual _ = false


    and prgEqual ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) = (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2, T.dot1 t2)))
      | prgEqual ((T.New P1), (T.New P2, t2)) = prgEqual(P1, (P2, t2))
      | prgEqual ((T.Choose P1), (T.Choose P2, t2)) = prgEqual(P1, (P2, t2))
      | prgEqual ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) = (Conv.conv((U1, I.id),(U2,(T.coerceSub t2))) andalso prgEqual((P1), (P2, t2)))
      | prgEqual ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) = (blockEqual(B1, (I.blockSub(B2, T.coerceSub t2))) andalso prgEqual(P1,(P2,t2)))

      | prgEqual ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) = (prgEqual(P1a, (P2a, t2)) andalso prgEqual(P1b, (P2b, t2)))

      | prgEqual ((T.Unit), (T.Unit, t2)) = true

      | prgEqual (T.Const lemma1, (T.Const lemma2, _)) = (lemma1=lemma2)

      | prgEqual (T.Var x1, (T.Var x2, t2)) =
                     (case getFrontIndex(T.varSub(x2,t2)) of
                           NONE => false
                         | SOME i => (x1 = i))

(*      | prgEqual ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) => ((lemma1=lemma2) andalso (spineEqual(S1, (S2,t2))))
                 |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => false
                            | SOME i => ((x1 = i) andalso (spineEqual(S1, (S2,t2)))))
                 |  _ => false)
*)
      | prgEqual ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) = (prgEqual(P1, (P2,t2)) andalso spineEqual(S1, (S2,t2)))

      | prgEqual ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) = (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2,T.dot1 t2)))

      | prgEqual ((T.Case (T.Cases O1)), (T.Case (T.Cases O2), t2)) = caseEqual(O1, (O2, t2))

      | prgEqual ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) = (decEqual(D1, (D2, t2)) andalso prgEqual(P1a, (P2a, t2)))

      | prgEqual ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) = (* there are no PClo created in converter *) raise Error "PClo should not exist!"

      | prgEqual ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) = raise Error "No EVARs should exist!"

      | prgEqual _ = false


    (* convertCases is where the real work comes in *)
    (* will attempt to merge cases together and call convert
     * on what happens in each case
     *)
    and convertCases (A::C) =
      let
        val ((Psi,t,P),C') = removeRedundancy(A,C)
      in
        ((Psi,t,convert(P))::convertCases(C'))
      end

      | convertCases C = C (* will be T.Cases nil *)


    (* Returns a list with C (merged with redundant cases) as the head followed by the rest *)
    and removeRedundancy (C, []) = (C, [])
      | removeRedundancy ( C, C'::rest) =
            let
              val (C''::Cs) = mergeIfNecessary(C, C')
              val (C''', rest') = removeRedundancy(C'', rest)
             in
              (C''', Cs @ rest')
            end

    (* returns NONE if not found *)
    and getFrontIndex (T.Idx k) = SOME(k)
      | getFrontIndex (T.Prg P) = getPrgIndex(P)
      | getFrontIndex (T.Exp U) = getExpIndex(U)
      | getFrontIndex (T.Block B) = getBlockIndex(B)
      | getFrontIndex (T.Undef) = NONE


    (* getPrgIndex returns NONE if it is not an index *)
    and getPrgIndex (T.Var k) = SOME(k)
      | getPrgIndex (T.Redex(P, T.Nil) ) = getPrgIndex(P)

      (* it is possible in the matchSub that we will get PClo under a sub (usually id) *)
      | getPrgIndex (T.PClo (P,t)) =
            (case getPrgIndex(P) of
              NONE => NONE
            | SOME i => getFrontIndex (T.varSub (i, t)))

      | getPrgIndex _ = NONE

    (* getExpIndex returns NONE if it is not an index *)
    and getExpIndex (I.Root (I.BVar k, I.Nil)) = SOME(k)
      | getExpIndex (I.Redex (U, I.Nil)) = getExpIndex(U)
      | getExpIndex (I.EClo (U, t)) =
            (case getExpIndex(U) of
               NONE => NONE
             | SOME i => getFrontIndex (T.revCoerceFront(I.bvarSub(i, t))))

      | getExpIndex (U as I.Lam (I.Dec (_, U1), U2)) = (SOME ( Whnf.etaContract(U) )  handle Whnf.Eta => NONE)
      | getExpIndex _ = NONE

    (* getBlockIndex returns NONE if it is not an index *)
    and getBlockIndex (I.Bidx k) = SOME(k)
      | getBlockIndex _ = NONE



    (* clean up the renaming substitution,
       this is to allow T.invertSub to appropriately
       think it is a pattern substitution
       *)
    and cleanSub (S as T.Shift _) = S
      | cleanSub (T.Dot(Ft1,s1)) =
         (case getFrontIndex(Ft1) of
            NONE => T.Dot(Ft1, cleanSub(s1))
          | SOME index =>  T.Dot(T.Idx index, cleanSub(s1)))


    (* determine if t is simply a renaming substitution *)
    and IsSubRenamingOnly (T.Shift(n)) = true
      | IsSubRenamingOnly (T.Dot(Ft1,s1)) =
          (case getFrontIndex(Ft1) of
             NONE => false
           | SOME _ => true)

          andalso IsSubRenamingOnly (s1)

    (* Note that what we are merging it with will need to go under an extra renaming substitution *)

    and mergeSpines ( (T.Nil), (T.Nil, t2) ) = T.Nil
      | mergeSpines ( (T.AppExp(E1,S1)), (T.AppExp(E2,S2), t2) ) =
            if Conv.conv( (E1,I.id), (E2, T.coerceSub(t2)) ) then
              T.AppExp(E1, mergeSpines(S1,(S2,t2)))
            else
              raise Error "Spine not equal (AppExp)"

      | mergeSpines ( (T.AppBlock (B1,S1)), (T.AppBlock(B2,S2), t2) ) =
            if blockEqual( B1, I.blockSub (B2, T.coerceSub t2))  then
              T.AppBlock(B1, mergeSpines(S1,(S2,t2)))
            else
              raise Error "Spine not equal (AppBlock)"

      | mergeSpines ( (T.AppPrg (P1,S1)), (T.AppPrg(P2,S2), t2) ) =
                if (prgEqual(P1, (P2, t2))) then
                  T.AppPrg(P1, mergeSpines(S1, (S2,t2)))
                else
                  raise Error "Prg (in App) not equal"

      | mergeSpines ( T.SClo(S,t1), (T.SClo(s,t2a), t2) ) =
(* there are no SClo created in converter *) raise Error "SClo should not exist!"

      | mergeSpines _ = raise Error "Spine are not equivalent"


    and mergePrgs ((T.Lam (D1, P1)), (T.Lam (D2, P2), t2)) =
                                if (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2, T.dot1 t2)))  then
                                   T.Lam(D1, P1)
                                else
                                    raise Error "Lambda don't match"

      | mergePrgs ((T.New P1), (T.New P2, t2)) = if (prgEqual(P1, (P2, t2))) then T.New P1 else
                                      raise Error "New don't match"

      | mergePrgs ((T.Choose P1), (T.Choose P2, t2)) = if (prgEqual(P1, (P2, t2))) then T.Choose P1 else
                                      raise Error "Choose don't match"

      | mergePrgs ((T.PairExp (U1, P1)), (T.PairExp (U2, P2), t2)) =
                        let
                          val t2' = T.coerceSub t2
                        in
                             if (Conv.conv((U1, I.id),(U2,t2'))) then
                                T.PairExp (U1, mergePrgs((P1), (P2, t2)))
                             else
                                raise Error "cannot merge PairExp"
                        end

      | mergePrgs ((T.PairBlock (B1, P1)), (T.PairBlock (B2, P2), t2)) =
                        let
                          val B2' = I.blockSub (B2, T.coerceSub t2)
                        in
                          if (blockEqual (B1, B2')) then
                                T.PairBlock (B1, mergePrgs((P1),(P2, t2)))
                          else
                                raise Error "cannot merge PairBlock"
                        end


      | mergePrgs ((T.PairPrg (P1a, P1b)), (T.PairPrg (P2a, P2b), t2)) =
                        if (prgEqual(P1a, (P2a, t2))) then
                          T.PairPrg (P1a, (mergePrgs( (P1b),(P2b, t2) )))
                        else
                          raise Error "cannot merge PairPrg"

      | mergePrgs ((T.Unit), (T.Unit, t2)) = T.Unit

      | mergePrgs (T.Const lemma1, (T.Const lemma2, _)) =
                   if (lemma1=lemma2) then T.Const lemma1
                   else raise Error "Constants do not match."

      | mergePrgs (T.Var x1, (T.Var x2, t2)) =
                     (case getFrontIndex(T.varSub(x2,t2)) of
                           NONE => raise Error "Variables do not match."
                         | SOME i =>
                             (if (x1 = i) then T.Var x1
                              else raise Error "Variables do not match."))

(*      | mergePrgs ((T.Root (H1, S1)), (T.Root (H2, S2), t2)) =
                (case (H1, H2)
                   of (T.Const lemma1, T.Const lemma2) =>
                     if (lemma1=lemma2) then
                        T.Root (H1, mergeSpines((S1),(S2,t2)))
                     else raise Error "Roots do not match"
                   |  (T.Var x1, T.Var x2) =>
                           (case getFrontIndex(T.varSub(x2,t2)) of
                              NONE => raise Error "Root does not match."
                            | SOME i =>
                                (if (x1 = i) then
                                   T.Root (T.Var x1, mergeSpines((S1),(S2,t2)))
                                 else
                                   raise Error "Root does not match."))
                   |  _ => raise Error "Root does not match.")
*)
      | mergePrgs ((T.Redex (P1, S1)), (T.Redex (P2, S2), t2)) =
        let
          val newS = mergeSpines(S1, (S2, t2))
        in
          if (prgEqual (P1, (P2, t2))) then
            T.Redex(P1, newS)
          else
            raise Error "Redex Prgs don't match"
        end

      | mergePrgs ((T.Rec (D1, P1)), (T.Rec (D2, P2), t2)) =
        if (decEqual(D1, (D2,t2)) andalso prgEqual(P1, (P2,T.dot1 t2)))  then
            T.Rec(D1, P1)
        else
          raise Error "Rec's don't match"

      | mergePrgs ( (T.Case (T.Cases O1)), (T.Case (T.Cases [C]), t2)) =
                (* check the case now *)
                (* three possible outcomes -
                   (1) We merge the cases together
                   (2) Cases are incompatible (duplicated)
                   (3) Cases are duplicate but all results are the same
                       which means we need to continue merging
                 *)
                T.Case (T.Cases (mergeCase(O1, (C,t2))))


      (* By invariant the second case should be a list of one *)
      | mergePrgs ((T.Case O1), (T.Case O2, t2)) = raise Error "Invariant Violated"


      | mergePrgs ((T.PClo (P1, t1)), (T.PClo (P2, t2a), t2b)) = (* there are no PClo created in converter *) raise Error "PClo should not exist!"


      | mergePrgs ((T.Let (D1, P1a, P1b)), (T.Let (D2, P2a, P2b), t2)) =
                if (decEqual(D1, (D2, t2)) andalso prgEqual(P1a, (P2a, t2))) then
                  T.Let(D1, P1a, mergePrgs((P1b), (P2b,T.dot1 t2)))
                else
                  raise Error "Let don't match"

      | mergePrgs ((T.EVar (Psi1, P1optRef, F1, _, _, _)), (T.EVar (Psi2, P2optref, F2, _, _, _), t2)) = raise Error "No EVARs should exist!"

      | mergePrgs _ = raise Error "Redundancy in cases could not automatically be removed."

(*
    (* For debug purposes *)
    and printCtx(Psi) =
      let
        fun printDec ( T.UDec (I.Dec (SOME(s), E)) ) =  (print s ; print ": "; print (Print.expToString (T.coerceCtx Psi, E)); print "\n" )
          | printDec ( T.UDec (I.BDec (SOME(s), (cid, sub)))) = (print s ; print ":\n")
          | printDec ( T.UDec (I.ADec (SOME(s), i))) = (print s ; print ":(ADec\n")
          | printDec ( T.UDec (I.NDec) ) = (print "(NDec)\n")
          | printDec ( T.PDec (SOME(s), F)) = (print s ; print ":(PDec)\n")
      in
        case Psi of
          (I.Null) => (print "Null\n")
          | (I.Decl (G, D)) =>  (printCtx(G) ; printDec(D))
      end
*)

    (* invertSub s = s'

       Invariant:
       If   G |- s : G'    (and s patsub)
       then G' |- s' : G
       s.t. s o s' = id
    *)
    and invertSub s =
      let
        fun lookup (n, T.Shift _, p) = NONE
          | lookup (n, T.Dot (T.Undef, s'), p) = lookup (n+1, s', p)
          | lookup (n, T.Dot (Ft, s'), p) =
              (case getFrontIndex(Ft) of
                 NONE => lookup (n+1, s', p)
               | SOME k => if (k=p) then SOME n else lookup (n+1, s', p))

        fun invertSub'' (0, si) = si
          | invertSub'' (p, si) =
            (case (lookup (1, s, p))
               of SOME k => invertSub'' (p-1, T.Dot (T.Idx k, si))
                | NONE => invertSub'' (p-1, T.Dot (T.Undef, si)))

        fun invertSub' (n, T.Shift p) = invertSub'' (p, T.Shift n)
          | invertSub' (n, T.Dot (_, s')) = invertSub' (n+1, s')
      in
        invertSub' (0, s)
      end



(* debug *)
    and printSub (T.Shift k) = print ("Shift " ^ Int.toString(k) ^ "\n")
      | printSub (T.Dot (T.Idx k, s)) = (print ("Idx " ^ Int.toString(k) ^ " (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Prg (T.EVar _), s)) = (print ("PRG_EVAR (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Exp (I.EVar _), s)) = (print ("EXP_EVAR (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Prg P, s)) = (print ("PRG (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Exp E, s)) = (print ("EXP (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Block B, s)) = (print ("BLOCK (DOT) " ) ; printSub(s))
      | printSub (T.Dot (T.Undef, s)) = (print ("UNDEF. (DOT) " ) ; printSub(s))


    (* We need to return it in terms of the context of the first *)
    and mergeCase ( [], C ) = raise Error "Case incompatible, cannot merge"

      | mergeCase (L as (Psi1, t1, P1)::O,  C as ((Psi2, t2, P2), tAfter)) =
      let

        (*
        val _ = printCtx(Psi1)
        val _ = printCtx(Psi2)
          *)

        (* Psi1 |- P1 : F[t1] *)
        (* Psi2 |- P2 : F[t2] *)

        (* Psi1 |- t1 : Psi1' *)
        (* Psi2 |- t2 : Psi2' *)

        (* By invariant,we assume *)
        (* Psi1' |- tAfter: Psi2' *)

        (* Psi2' |- tAfterInv : Psi1' *)

        val tAfterInv = T.invertSub(tAfter)


        val t3 = T.comp(tAfterInv, t2)

        (* So now we have
         P1 makes sense in Psi1, t1 goes from Psi1' to Psi1.

         Psi1 |- t1 : Psi1'
         Psi2 |- t3 : Psi1'
         *)

        val t = Opsem.createVarSub (Psi1, Psi2) (* Psi1 |- t : Psi2 *)
        val t' = T.comp (t3, t) (* Psi1 |- t' : Psi1' *)

        (* If we can get this to match, then Psi1 |- P2[t] *)
        val doMatch = (Opsem.matchSub (Psi1, t1, t') ; true)
          handle NoMatch => false

      in
        if (doMatch) then
          let
            val newT = T.normalizeSub t
            val stillMatch = IsSubRenamingOnly(newT)
          in
            if (stillMatch) then
          (* Since the case matches, lets continue the merge on P1 and P2
           * Note that removing the redundancy of other case statements
           * is handled recursively ... see convertCases
           *)
              (* Note that tAfter and newT are both renaming substitutions *)
              (Psi1, t1, mergePrgs(P1,(P2,cleanSub(newT))))::O
            else
              if (length(O) = 0) then
                (* We tried all the cases, and we can now add it *)
                (Psi2, t3, P2)::L
              else
                (* Try other cases *)
                (Psi1, t1, P1)::mergeCase(O,C)
          end

        else
          if (length(O) = 0) then
            (* We tried all the cases, and we can now add it *)
            (Psi2, t3, P2)::L

          else
            (* Try other cases *)
            (Psi1, t1, P1)::mergeCase(O,C)
      end

  (* mergeIfNecessary
   * Simply see if C is the same case as C'
   * If so, try to merge them together and return a list of just the case merged together,
   * otherwise, return a list of both elements.
   *)
    and mergeIfNecessary(C as (Psi1, s1, P1), C' as (Psi2, s2, P2)) =
      let
     (* Note that s1 is a substitution s.t.  Psi1 |- s1: Psi0
        and s2 is a substitution s.t.         Psi2 |- s2: Psi0

        It is possible that this property is lost when the case is executed
        with a different Psi0 which can happen during recursive calls
        (as the context grows).

        In that case:
          Psi, Psi1 |- X1...Xn, id{Psi} : Psi, Psi2

        Therefore, the X's are not dependent on the extra Psi introduced
        by recursive calls, which is why they are ignored in matchSub as well.

        We will generate a substitution t s.t. Psi1 |- t: Psi2
        Therefore  Psi1 |- (s2 o t) : Psi0

        And we are trying to match it with
                   Psi1 |- s1 : Psi0

      *)

        val t = Opsem.createVarSub (Psi1, Psi2) (* Psi1 |- t : Psi2 *)

        val t' = T.comp (s2, t)
     (* Now since s1 and t' go between the same contexts, we see
      * if we can unify them
      *)
        val doMatch = (Opsem.matchSub (Psi1, s1, t') ; true)
          handle NoMatch => false

      in
        if (not doMatch) then
          [C,C']
        else
          let
            val newT = T.normalizeSub t
          in
            if (IsSubRenamingOnly(newT)) then
              [(Psi1, s1, mergePrgs((P1), (P2, cleanSub(newT))))]
              (* In this case, C' is redundant and cannot be fixed, so C' will never be called
               * [C,C']
               *)
              handle Error s => (* (print ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n") ; [C]) *)
                raise Error  ("***WARNING*** -- redundant case automatically ANNIHILATED:  " ^ s ^ "\n")
            else
              [C,C']

          end

      end


  end