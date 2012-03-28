(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

functor Split
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
       ) : SPLIT =

struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  local
    structure T = Tomega
    structure I = IntSyn
    structure S = State'

    datatype Operator =
      Split of T.Prg option ref * T.Prg * string

    (* weaken (G, a) = w'

       Invariant:
       If   a is a type family
       then G |- w' : G'
       and  forall x:A in G'  A subordinate to a
     *)
    fun weaken (I.Null, a) = I.id
      | weaken (I.Decl (G', D as I.Dec (name, V)), a) =
        let
          val w' = weaken (G', a)
        in
          if Subordinate.belowEq (I.targetFam V, a) then I.dot1 w'
          else I.comp (w', I.shift)
        end
      (* added next case, probably should not arise *)
      (* Sun Dec 16 10:42:05 2001 -fp !!! *)
      (*
      | weaken (I.Decl (G', D as I.BDec _), a) =
           I.dot1 (weaken (G', a))
      *)

    (* createEVar (G, V) = X[w] where G |- X[w] : V

       Invariant:
       If G |- V : L
       then G |- X[w] : V
    *)
    fun createEVar (G, V) =
        let (* G |- V : L *)
          val w = weaken (G, I.targetFam V)       (* G  |- w  : G'    *)
          val iw = Whnf.invert w                  (* G' |- iw : G     *)
          val G' = Whnf.strengthen (iw, G)
          val X' = I.newEVar (G', I.EClo (V, iw)) (* G' |- X' : V[iw] *)
          val X = I.EClo (X', w)                  (* G  |- X  : V     *)
        in
          X
        end


    (* instEVars ({x1:V1}...{xp:Vp} V, p, nil) = (V[s], [X1,...,Xn])
       where . |- s : {x1:V1}...{xp:Vp}
       and s = Xp...X1.id, all Xi are new EVars
    *)
    fun instEVars (Vs, p, XsRev) = instEVarsW (Whnf.whnf Vs, p, XsRev)
    and instEVarsW (Vs, 0, XsRev) = (Vs, XsRev)
      | instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), p, XsRev) =
        let (* p > 0 *)
          val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
        in
          instEVars ((V2, I.Dot (I.Exp (X1), s)), p-1, SOME(X1)::XsRev)
        end
      | instEVarsW ((I.Pi ((I.BDec (_, (l, t)), _), V2), s), p, XsRev) =
        (* G0 |- t : Gsome *)
        (* . |- s : G0 *)
        let (* p > 0 *)
          val L1 = I.newLVar (I.Shift(0), (l, I.comp(t,s))) (* --cs Sun Dec  1 06:33:27 2002 *)
        in
          instEVars ((V2, I.Dot (I.Block (L1), s)), p-1, NONE::XsRev)
        end

    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local
      val caseList : (T.Dec I.Ctx * T.Sub) list ref = ref nil
    in
      fun resetCases () = (caseList := nil)
      fun addCase (Psi, t) = (caseList := (Psi, t) :: !caseList)
      fun getCases () = (!caseList)
    end

    (* createEVarSpine (G, (V, s)) = (S', (V', s'))

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =
        let (* G |- V1[s] : L *)
          val X = createEVar (G, I.EClo (V1, s))
          val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
        in
          (I.App (X, S), Vs)
        end
      (* Uni or other cases should be impossible *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant:
       If   S |- c : Pi {V1 .. Vn}. V
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H as I.Const (cid)) =
        let
          val V = I.constType cid
          val (S, Vs) = createEVarSpine (G, (V, I.id))
        in
          (I.Root (H, S), Vs)
        end

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant:
       If   G |- k : Pi {V1 .. Vn}. V
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
        let
          val I.Dec (_, V) = I.ctxDec (G, k)
          val (S, Vs) = createEVarSpine (G, (V, I.id))
        in
          (I.Root (I.BVar (k), S), Vs)
        end


    (* createAtomProj (G, #i(l), (V, s)) = (U', (V', s'))

       Invariant:
       If   G |- #i(l) : Pi {V1 .. Vn}. Va
       and  G |- Pi {V1..Vn}. Va = V[s] : type
       then . |- U' = #i(l) @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomProj (G, H, (V, s)) =
        let
          val (S, Vs') = createEVarSpine (G, (V, s))
        in
          (I.Root (H, S), Vs')
        end

    fun constCases (G, Vs, nil, sc) = ()
      | constCases (G, Vs, I.Const(c)::sgn', sc) =
        let
          val (U, Vs') = createAtomConst (G, I.Const c)
          val _ = CSManager.trail (fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else ())
        in
          constCases (G, Vs, sgn', sc)
        end

    fun paramCases (G, Vs, 0, sc) = ()
      | paramCases (G, Vs, k, sc) =
        let
          val (U, Vs') = createAtomBVar (G, k)
          val _ = CSManager.trail (fn () =>
                                   if Unify.unifiable (G, Vs, Vs')
                                     then sc U
                                   else ())
        in
          paramCases (G, Vs, k-1, sc)
        end

    (* createEVarSub G' = s

       Invariant:
       If   . |- G' ctx
       then . |- s : G' and s instantiates each x:A with an EVar . |- X : A

       Update: Always use empty context. Sat Dec  8 13:19:58 2001 -fp
    *)
    fun createEVarSub (I.Null) = I.id
      | createEVarSub (I.Decl(G', D as I.Dec (_, V))) =
        let
          val s = createEVarSub G'
          val V' = I.EClo (V, s)
          val X = I.newEVar (I.Null, V')
        in
          I.Dot (I.Exp X, s)
        end

    (* hack *)
    fun blockName (cid) = I.conDecName (I.sgnLookup (cid))

    (* blockCases (G, Vs, B, (Gsome, piDecs), sc) =

       If G |- V[s] : type
          . |- Gsome ctx and Gsome |- piDecs decList
       then sc is called for any x:A in piDecs such thtat
            G |- V[s] = A[t] : type
            where t instantiates variable in Gsome with new EVars
    *)
    fun blockCases (G, Vs, cid, (Gsome, piDecs), sc) =
        let
          val t = createEVarSub Gsome   (* accounts for subordination *)
          (* . |- t : Gsome *)
          val sk = I.Shift (I.ctxLength(G))
          val t' = I.comp (t, sk)
          val lvar = I.newLVar (sk, (cid, t'))  (* --cs Sun Dec  1 06:33:41 2002 *)
          (* G |- t' : Gsome *)
        in
          blockCases' (G, Vs, (lvar, 1), (t', piDecs), sc)
        end
    and blockCases' (G, Vs, (lvar, i), (t, nil), sc) = ()
      | blockCases' (G, Vs, (lvar, i), (t, I.Dec (_, V')::piDecs), sc) =
        let
          (* G |- t : G' and G' |- ({_:V'},piDecs) decList *)
          (* so G |- V'[t'] : type *)
          val (U, Vs') = createAtomProj (G, I.Proj (lvar, i), (V', t))
          val _ = CSManager.trail (fn () => if Unify.unifiable (G, Vs, Vs')
                                              then sc U
                                            else ())
          val t' = I.Dot (I.Exp (I.Root (I.Proj (lvar, i), I.Nil)), t)
        in
          blockCases' (G, Vs, (lvar, i+1), (t', piDecs), sc)
        end

    fun worldCases (G, Vs, T.Worlds (nil), sc) = ()
      | worldCases (G, Vs, T.Worlds (cid::cids), sc) =
          ( blockCases (G, Vs, cid, I.constBlock cid, sc) ;
            worldCases (G, Vs, T.Worlds (cids), sc) )

    fun lowerSplit (G, Vs, W, sc) = lowerSplitW (G, Whnf.whnf Vs, W, sc)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), W, sc) =
        let
          val _ = constCases (G, Vs, Index.lookup a, sc) (* will trail *)
          val _ = paramCases (G, Vs, I.ctxLength G, sc) (* will trail *)
          val _ = worldCases (G, Vs, W, sc) (* will trail *)
        in
          ()
        end
 (*     | lowerSplitW (G, (I.Pi ((D, P), V), s), W, sc) =
        let
          val D' = I.decSub (D, s)
        in
          lowerSplit (I.Decl (G, D'), (V, I.dot1 s), W, fn U => sc (I.Lam (D', U)))
        end
      we assume that all EVars are lowere :-)
*)

    (* splitEVar (X, W, sc) = ()

       calls sc () for all cases, after instantiation of X
       W are the currently possible worlds
    *)
    fun splitEVar ((X as I.EVar (_, GX, V, _)), W, sc) = (* GX = I.Null *)
          lowerSplit (I.Null, (V, I.id), W,
                      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id))
                                then sc ()
                              else ())

    (* createSub (Psi) = s

       Invariant:
       If   Psi is a meta context
       then s = Xp...X1.id, all Xi are new EVars/LVars/MVars
       and  . |- s : Psi
    *)
    fun createSub (I.Null) = (T.id)
      | createSub (I.Decl (Psi, T.UDec (I.Dec (xOpt, V1)))) =
        let
          val (t') = createSub Psi
          val X = I.newEVar (I.Null, I.EClo (Whnf.whnf (V1, T.coerceSub t'))) (* all EVars are global and lowered *)
        in
           (T.Dot (T.Exp X, t'))
        end
      | createSub (I.Decl (Psi, T.UDec (I.BDec (_, (l, s))))) =
        (* Psi0 |- t : Gsome *)
        (* . |- s : Psi0 *)
        let
          val (t') = createSub Psi
          val L = I.newLVar (I.Shift(0), (l, I.comp(s, T.coerceSub t')))
                                        (* --cs Sun Dec  1 06:34:00 2002 *)
        in
          (T.Dot (T.Block L, t'))
        end
      | createSub (I.Decl (Psi, T.PDec (_, F, TC1, TC2))) =
        let (* p > 0 *)
          val t' = createSub Psi
          val Y = T.newEVarTC (I.Null, T.FClo (F, t'), TC1, TC2)
        in
          (T.Dot (T.Prg Y, t'))
        end


    (* mkCases L F= Ss

       Invariant:
       If   L is a list of cases (Psi1, t1) .... (Psin, tn)
       and  Psii |- ti : Psi
       and  Psi  |- F formula
       then Ss is a list of States S1 ... Sn
       and  Si = (Psii, Fi)
       where  Psii |- Fi = F [ti]  formula
    *)

    fun mkCases (nil, F) = nil
      | mkCases ((Psi, t) :: cs, F) =
        let
          val X = T.newEVar (Psi, T.FClo (F, t))
        in
          (Psi, t, X) :: mkCases (cs, F)
        end


    (* split S = S1 ... Sn

       Invariant:
       If   S = (P |> F)
       then Si = (Pi |> Fi)
       s.t. there exists substitution si
            and  Pi |- si : P
            and  Pi |- Fi = F[si]
            and  for every G |- t : P,

                 there ex. an i among 1..n
                 and a substitution t',
                 s.t. G |- t' : Pi
                 and  t = t' [si]
    *)

    fun split (S.Focus (T.EVar (Psi, r, F, NONE, NONE, _), W)) =
      let

        (* splitXs (G, i) (Xs, F, W, sc) = Os
           Invariant:
           If   Psi is a CONTEXT
           and  G ~ Psi a context,
           and  G |- i : V
           and  Psi |- F formula
           and  Xs are all logic variables
           then Os is a list of splitting operators
        *)
        fun splitXs (G, i) (nil, _, _, _) = nil
          | splitXs (G, i) (X :: Xs, F, W, sc) =
            let
              val _ = if !Global.chatter >= 6
                        then print ("Split " ^ Print.expToString (I.Null, X) ^ ".\n")
                      else ()
              val Os = splitXs (G,i+1) (Xs, F, W, sc)    (* returns a list of operators *)
              val _ = resetCases ()
(*            val I.Dec (SOME s, _) = I.ctxLookup (G, i) *)
              val s = Print.expToString (G, X)
              val Os' = (splitEVar (X, W, sc);
                         Split (r, T.Case (T.Cases (mkCases (getCases (), F))), s) :: Os)
                handle  Constraints.Error (constrs) =>
                  (if !Global.chatter >= 6
                     then print ("Inactive split:\n" ^ Print.cnstrsToString (constrs) ^ "\n")
                   else ();
                     Os)
            in
              Os'
            end

        val t = createSub Psi  (* . |- t :: Psi *)
        val Xs = State.collectLFSub t
        fun init () = (addCase (Abstract.abstractTomegaSub t))
        val G = T.coerceCtx Psi
        val Os = splitXs (G, 1) (Xs, F, W, init)
      in
        Os
      end

    fun expand (S as S.Focus (T.EVar (Psi, r, F, NONE, NONE, _), W)) =
      if Abstract.closedCTX Psi then split S else []

    (* apply (Op) = Sl'

       Invariant:
       If   Op = (_, Sl)
       then Sl' = Sl

       Side effect: If Sl contains inactive states, an exception is raised
    *)
    fun apply (Split (r, P, s)) = (r := SOME P)    (* trailing required -cs Thu Apr 22 12:05:04 2004 *)
    fun menu (Split (_, _, s)) = "Split " ^ s
  in
    type operator = Operator

    val expand = expand
    val apply = apply
    val menu = menu
  end
end (* functor Split *)