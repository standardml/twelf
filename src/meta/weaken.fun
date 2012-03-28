(* Weakening substitutions *)
(* Author: Carsten Schuermann *)

functor Weaken ((*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                  ) : WEAKEN =
struct
  (*! structure IntSyn = IntSyn' !*)

  local
    structure I = IntSyn

    (* strengthenExp (U, s) = U'

       Invariant:
       If   G |- s : G'
       and  G |- U : V
       then G' |- U' = U[s^-1] : V [s^-1]
    *)
    fun strengthenExp (U, s) = Whnf.normalize (Whnf.cloInv (U, s), I.id)

    (* strengthenDec (x:V, s) = x:V'

       Invariant:
       If   G |- s : G'
       and  G |- V : L
       then G' |- V' = V[s^-1] : L
    *)
    fun strengthenDec (I.Dec (name, V), s) = I.Dec (name, strengthenExp (V, s))

    (* strengthenCtx (G, s) = (G', s')

       If   G0 |- G ctx
       and  G0 |- s G1
       then G1 |- G' = G[s^-1] ctx
       and  G0 |- s' : G1, G'
    *)
    fun strengthenCtx (I.Null, s) = (I.Null, s)
      | strengthenCtx (I.Decl (G, D), s) =
        let
          val (G', s') = strengthenCtx (G, s)
        in
          (I.Decl (G', strengthenDec (D, s')), I.dot1 s')
        end

    fun strengthenSub (s, t) = Whnf.compInv (s, t)

    fun strengthenSpine (I.Nil, t) = I.Nil
      | strengthenSpine (I.App (U, S), t) = I.App (strengthenExp (U, t), strengthenSpine (S, t))

  in
    val strengthenExp = strengthenExp
    val strengthenSpine = strengthenSpine
    val strengthenDec = strengthenDec
    val strengthenCtx = strengthenCtx
    val strengthenSub = strengthenSub
  end
end (* functor Weaken *)
