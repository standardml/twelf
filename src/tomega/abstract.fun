(* Converter from relational representation to a functional
   representation of proof terms *)
(* Author: Carsten Schuermann *)

functor TomegaAbstract
  (structure Global : GLOBAL
   structure Abstract : ABSTRACT
   structure Whnf : WHNF
   structure Subordinate : SUBORDINATE)
     : TOMEGAABSTRACT =
struct

  exception Error of string


  local
    structure T = Tomega
    structure I = IntSyn
    structure M = ModeSyn
    structure S = Subordinate
    structure A = Abstract






    fun shiftCtx (I.Null, t) = (I.Null, t)
      | shiftCtx (I.Decl (G, D), t) =
        let
          val (G', t') =  shiftCtx (G, t)
        in
          (I.Decl (G', I.decSub (D, t')), I.dot1 t')
        end

    (* dotn (t, n) = t'

       Invariant:
       If   Psi0 |- t : Psi
       and  |G| = n   for any G
       then Psi0, G[t] |- t : Psi, G
    *)
    fun dotn (t, 0) = t
      | dotn (t, n) = I.dot1 (dotn (t, n-1))


    fun strengthenToSpine (I.Shift _ (* =0 *), 0, (n, S)) = S
      | strengthenToSpine (I.Dot (I.Idx _ (* = 1 *), t), l, (n, S)) =
        let
          val t' = I.comp (t, I.invShift)
        in
          strengthenToSpine (t', l-1, (n+1, I.App (I.Root (I.BVar n, I.Nil), S)))
        end
      | strengthenToSpine (I.Dot (I.Undef, t), l, (n, S)) =
          strengthenToSpine (t, l-1, (n+1, S))
      | strengthenToSpine (I.Shift k, l, (n, S)) =
          strengthenToSpine (I.Dot (I.Idx (k+1), I.Shift (k+1)), l, (n, S))



    (* raiseFor (B, (F, t)) = (P', F'))

       Invariant:
       If   Psi, B, G |-  F for
       and  Psi, G', B' |- t : Psi, B, G
       then Psi, G' |-  F' for
       and  F' = raise (B', F[t])   (using subordination)
    *)
    fun raiseFor (B', (T.True, t)) = T.True
      | raiseFor (B', (T.And (F1, F2), t)) =
        let
          val F1' = raiseFor (B', (F1, t))
          val F2' = raiseFor (B', (F2, t))
        in
          T.And (F1', F2')
        end
      | raiseFor (B', (T.Ex ((I.Dec (x, V), Q), F), t)) =
                                                    (* Psi, G', B' |- V[t] : type *)
                                                    (* Psi, B, G, x:V |- F for *)
                                                    (* Psi, G' |- B' ctx  *)
        let
(*        val (w, S) = subweaken (B', 1, I.targetFam V, I.Nil)     *)
          val w = S.weaken (B', I.targetFam V)
                                                   (* B'  |- w  : B''    *)
          val iw = Whnf.invert w                    (* B'' |- iw : B'     *)
          val B'' = Whnf.strengthen (iw, B')        (* Psi0, G' |- B'' ctx *)

          val V' = A.raiseType (B'', I.EClo (V, I.comp (t, iw))) (* Psi0, G' |- V' : type *)


          val (B''', _) = shiftCtx (B', I.shift)
                                                    (* Psi, G', x: V' |- B''' ctx *)

          val t'' = dotn (I.shift, I.ctxLength B')
                                                    (* Psi, G', x: V', B''' |- t'' :   Psi, G', B' *)
                                                    (* Psi, G', B' |- t : Psi, B, G  *)
          val t' = I.comp (t, t'')
                                                    (* Psi, G', x:V', B''' |- t' : Psi, B, G *)

                                                    (* Psi, G', x:V', B''' |- w : Psi,G', x:V', B'''' *)
          val S = strengthenToSpine (iw, I.ctxLength B', (1, I.Nil))
                                                    (* Psi, G', x:V', B''' |- S : V' [^|B'''|] >> type  *)
          val U = I.Root (I.BVar (I.ctxLength B''' + 1), S)
                                                    (* Psi, G', x:V', B''' |- U : V[t'] *)

          val t''' = Whnf.dotEta (I.Exp U, t')            (* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
          val F' = raiseFor (B''', (F, t'''))       (* Psi, G', x:V' |- F' for*)
        in
          T.Ex ((I.Dec (x, V'), Q), F')(* Psi, G', x:V', B''' |- t''' :  Psi, B, G, x:V *)
        end
      | raiseFor (_, (T.All _, _)) = raise Domain


    (* raisePrg (G, P, F) = (P', F'))

       Invariant:
       If   Psi, G |- P in F
       and  Psi |- G : blockctx
       then Psi |- P' in F'
       and  P = raise (G, P')   (using subordination)
       and  F = raise (G, F')   (using subordination)
    *)
    fun raisePrg (G, (T.Unit, t), _) = T.Unit
      | raisePrg (G, (T.PairPrg (P1, P2), t), T.And (F1, F2)) =
        let
          val P1' = raisePrg (G, (P1, t), F1)
          val P2' = raisePrg (G, (P2, t), F2)
        in
          T.PairPrg (P1', P2')
        end
      | raisePrg (G, (T.PairExp (U, P), t), T.Ex ((I.Dec (_, V), _), F)) =
        let
          val w = S.weaken (G, I.targetFam V)
                                                   (* G  |- w  : G'    *)
          val iw = Whnf.invert w                    (* G' |- iw : G     *)
          val G' = Whnf.strengthen (iw, G)        (* Psi0, G' |- B'' ctx *)

          val U' = A.raiseTerm (G', I.EClo (U, I.comp (t, iw)))
          val P' = raisePrg (G, (P, t), F)
        in
          T.PairExp (U', P')
        end


    fun raiseP (G, P, F) =
      let
        val (G', s) = T.deblockify G
(*      val P' = T.normalizePrg (P, s) (* G' |- P' : F' *) *)
        val F' = T.forSub (F, s)
        val P'' = raisePrg (G', (P, T.coerceSub s), F')
      in
        P''
      end

    fun raiseF (G, (F, t)) =
      let
        val (G', s) = T.deblockify G
        val F' = raiseFor (G', (F, I.comp (t, T.coerceSub s)))
      in
        F'
      end



  in
    val raisePrg = fn (G, P, F) => raisePrg (G, (P, I.id), F)
    val raiseP = raiseP
    val raiseFor = raiseFor
    val raiseF = raiseF
  end
end (* functor TomegaAbstract *)
