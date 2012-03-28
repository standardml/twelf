(* Skolem constant administration *)
(* Author: Carsten Schuermann *)

functor Skolem (structure Global : GLOBAL
                (*! structure IntSyn' : INTSYN !*)
                structure Whnf : WHNF
                (*! sharing Whnf.IntSyn = IntSyn' !*)
                structure Abstract : ABSTRACT
                (*! sharing Abstract.IntSyn = IntSyn' !*)
                structure IndexSkolem : INDEX
                (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
                structure ModeTable : MODETABLE
                (*! sharing ModeSyn.IntSyn = IntSyn' !*)
                structure Print : PRINT
                (*! sharing Print.IntSyn = IntSyn' !*)
                structure Compile : COMPILE
                (*! sharing Compile.IntSyn = IntSyn' !*)
                structure Timers : TIMERS
                structure Names : NAMES
                (*! sharing Names.IntSyn = IntSyn' !*)
                  )
  : SKOLEM =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    (*! structure CompSyn = Compile.CompSyn !*)

    (* installSkolem (name, k, (V, mS), L) =

       Invariant:
            name is the name of a theorem
       and  imp is the number of implicit arguments
       and  V is its term together with the mode assignment mS
       and  L is the level of the declaration

       Effects: New Skolem constants are generated, named, and indexed
    *)
    fun installSkolem (name, imp, (V, mS), L) =
      let
        (* spine n = S'

           Invariant:
           S' = n; n-1; ... 1; Nil
        *)
        fun spine 0 = I.Nil
          | spine n = I.App (I.Root (I.BVar n, I.Nil),  spine (n-1))

        (* installSkolem' ((V, mS), s, k) = ()

           Invariant:
                G |- V : type
           and  G' |- s : G
           and  |G'| = d
           and  k is a continuation, mapping a type G' |- V' type
                to . |- {{G'}} V'

           Effects: New Skolem constants are generated, named, and indexed
        *)

        fun installSkolem' (d, (I.Pi ((D, DP), V), mS), s, k) =
            (case mS
               of M.Mapp (M.Marg (M.Plus, _), mS') =>
                    installSkolem' (d+1, (V, mS'), I.dot1 s,
                                    fn V => k (Abstract.piDepend ((Whnf.normalizeDec (D, s), I.Meta), V)))
(*                                  fn V => k (I.Pi ((Whnf.normalizeDec (D, s), DP), V))) *)
                | M.Mapp (M.Marg (M.Minus, _), mS') =>
                  let
                    val I.Dec (_, V') = D
                    val V'' = k (Whnf.normalize (V', s))
                    val name' = Names.skonstName (name ^ "#")
                    val SD = I.SkoDec (name', NONE, imp, V'', L)
                    val sk = I.sgnAdd SD
                    val H = I.Skonst sk
                    val _ = IndexSkolem.install I.Ordinary H
                    val _ = Names.installConstName sk
                    val _ = (Timers.time Timers.compiling Compile.install) I.Ordinary sk
(*                  val CompSyn.SClause r = CompSyn.sProgLookup sk *)
                    val S = spine d
                    val _ = if !Global.chatter >= 3
                              then TextIO.print (Print.conDecToString SD ^ "\n")
                            else ()
                  in
                    installSkolem' (d, (V, mS'), I.Dot (I.Exp (I.Root (H, S)), s), k)
                  end)
          | installSkolem' (_, (I.Uni _, M.Mnil), _, _) = ()


      in
        installSkolem' (0, (V, mS), I.id, fn V => V)
      end

    (* install L = ()

       Invariant:
           L is a list of a's (mututal inductive theorems)
           which have an associated mode declaration

       Effect: Skolem constants for all theorems are generated, named, and indexed
    *)
    fun install nil = ()
      | install (a :: aL) =
        let
          val I.ConDec (name, _, imp, _, V, L) = I.sgnLookup a
          val SOME mS = ModeTable.modeLookup a
          val _ = installSkolem (name, imp, (V, mS), I.Type)
        in
          install aL
        end


  in
    val install = install
  end (* local *)
end (* functor Skolem *)
