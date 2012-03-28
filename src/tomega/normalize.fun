(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

functor Normalize
  (structure IntSyn' : INTSYN
   structure Tomega' : TOMEGA
     sharing Tomega'.IntSyn = IntSyn'
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
) : NORMALIZE =
struct
  structure IntSyn = IntSyn'
  structure Tomega = Tomega'

  exception Error of string

  local
    structure I = IntSyn'
    structure T = Tomega'

    fun normalizeFor (T.All (D, F), t) =
          T.All (T.decSub (D, t),
                 normalizeFor (F, T.dot1 t))
      | normalizeFor (T.Ex (D, F), t) =
          T.Ex (I.decSub (D, T.coerceSub t),
                 normalizeFor (F, T.dot1 t))
      | normalizeFor (T.And (F1, F2), t) =
          T.And (normalizeFor (F1, t),
                 normalizeFor (F2, t))
      | normalizeFor (T.FClo (F, t1), t2) =
          normalizeFor (F, T.comp (t1, t2))
      | normalizeFor (T.World (W, F), t) =
          T.World (W, normalizeFor (F, t))
(*      | normalizeFor (T.FVar (G, r))   think about it *)
      | normalizeFor (T.True, _) = T.True


    (* normalizePrg (P, t) = (P', t')

       Invariant:
       If   Psi' |- P :: F
       and  Psi  |- t :: Psi'
       and  P doesn't contain free EVars
       then there exists a Psi'', F'
       s.t. Psi'' |- F' for
       and  Psi'' |- P' :: F'
       and  Psi |- t' : Psi''
       and  Psi |- F [t] == F' [t']
       and  Psi |- P [t] == P' [t'] : F [t]
       and  Psi |- P' [t'] :nf: F [t]
    *)

    fun normalizePrg (P as (T.Root (T.Const _,_)), t) = P
      | normalizePrg ((P as (T.Root (T.Var n, _))), t) =
           normalizePrg (P, T.Dot (T.varSub (n, t), T.id))
      | normalizePrg (T.Lam (D, P'), t) = T.Lam (D, normalizePrg (P', T.dot1 t))
      | normalizePrg (T.PairExp (U, P'), t) =
          T.PairExp (I.EClo (Whnf.whnf ((U, T.coerceSub t) : I.eclo)), normalizePrg (P', t))
(*      | normalizePrg (T.PairBlock (B, P'), t) =
          T.PairBlock (B, normalizePrg P') *)
      | normalizePrg (T.PairPrg (P1, P2), t) =
          T.PairPrg (normalizePrg (P1, t), normalizePrg (P2, t))
      | normalizePrg (T.Unit, _) = T.Unit
      | normalizePrg (T.Redex (P, S), t) =
          T.Redex (normalizePrg (P, t), normalizeSpine S)
          (* Clearly, the redex should be removed here *)
      | normalizePrg (T.Rec (D, P), t) = T.Rec (D, normalizePrg (P, t))
      | normalizePrg (P as T.Case _, t) = P
      | normalizePrg (P as T.EVar (Psi, ref (SOME P'), _), t) = normalizePrg (P', t)

    and normalizeSpine T.Nil = T.Nil
      | normalizeSpine (T.AppExp (U, S)) =
          T.AppExp (U, normalizeSpine S)
     | normalizeSpine (T.AppPrg (P, S)) =
          T.AppPrg (normalizePrg (P, T.id), normalizeSpine S)
      | normalizeSpine (T.AppBlock (B, S)) =
          T.AppBlock (B, normalizeSpine S)

(*
    and normalizeDec (T.UDec D, t) = T.UDec (I.decSub (D, T.coerceSub t))
(*      | normalizeDec (T.BDec (k, t1), t2) = *)
      | normalizeDec (T.PDec (n, F), t) = T.PDec (n, (normalizeFor (F, t)))
*)

    fun normalizeSub (s as T.Shift n) = s
      | normalizeSub (T.Dot (T.Prg P, s)) =
          T.Dot (T.Prg (normalizePrg (P, T.id)), normalizeSub s)
      | normalizeSub (T.Dot (F, s)) =
          T.Dot (F, normalizeSub s)
  in
    val normalizeFor = normalizeFor
    val normalizePrg = normalizePrg
    val normalizeSpine = normalizeSpine
    val normalizeSub = normalizeSub
  end
end
