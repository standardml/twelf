(* Inference:  Version 1.3*)
(* Author: Carsten Schuermann *)

functor Inference (structure MTPGlobal : MTPGLOBAL
                   (*! structure IntSyn : INTSYN !*)
                   (*! structure FunSyn' : FUNSYN !*)
                   (*! sharing FunSyn'.IntSyn = IntSyn !*)
                   structure StateSyn' : STATESYN
                   (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                   structure Abstract : ABSTRACT
                   (*! sharing Abstract.IntSyn = IntSyn !*)
                   structure TypeCheck : TYPECHECK
                   (*! sharing TypeCheck.IntSyn = IntSyn !*)
                   structure FunTypeCheck : FUNTYPECHECK
                   (*! sharing FunTypeCheck.FunSyn = FunSyn' !*)
                     sharing FunTypeCheck.StateSyn = StateSyn'
                   structure UniqueSearch  : UNIQUESEARCH
                   (*! sharing UniqueSearch.IntSyn = IntSyn !*)
                   (*! sharing UniqueSearch.FunSyn = FunSyn' !*)
                     sharing UniqueSearch.StateSyn = StateSyn'
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                     )
  : INFERENCE =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string

  type operator = (unit -> StateSyn'.State)

  local
    structure S = StateSyn
    structure F = FunSyn
    structure I = IntSyn

    exception Success

    (* createEVars (G, (F, V, s)) = (Xs', (F', V', s'))

       Invariant:
       If   |- G ctx
       and  G0 |- F = {{x1:A1}} .. {{xn::An}} F1 formula
       and  G0 |- V = { x1:A1}  .. {xn:An} V1 : type
       and  G |- s : G0
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G |- s: G'
       and  G0 |- F' = F1 for
       and  G0 |- V' = V1 : type
    *)
    fun createEVars (G, (I.Pi ((I.Dec (_, V), I.Meta), V'), s)) =
        let
          val X = I.newEVar (G, I.EClo (V, s))
          val X' = Whnf.lowerEVar X
          val (Xs, FVs') = createEVars (G, (V', I.Dot (I.Exp X, s)))
        in
          (X' :: Xs, FVs')
        end
      | createEVars (G, FVs as (_, s)) = (nil, FVs)



    (* forward (G, B, (V, F)) = (V', F')  (or none)

       Invariant:
       If   |- G ctx
       and  G |- B tags
       and  G |- V type
       and  G; . |- F : formula
       then G |- V' type
       and  G; . |- F' : formula

    *)
    fun forward (G, B, V as I.Pi ((_, I.Meta), _)) =
        let
          val _ = if !Global.doubleCheck
                    then TypeCheck.typeCheck (G, (V, I.Uni I.Type))
                    else ()
          val (Xs, (V', s')) = createEVars (G, (V, I.id))
        in
          (case  UniqueSearch.searchEx (2, Xs, fn nil => [(Whnf.normalize (V', s'))]
                                                | _ => raise UniqueSearch.Error "Too many solutions")
             of [VF''] => SOME VF''

              | [] => NONE) handle UniqueSearch.Error _ => NONE
        end
      | forward (G, B, V) = NONE



    (* expand' ((G, B), n) = ((Gnew, Bnew), sc)

       Invariant:
       If   |- G0 ctx    G0 |- B0 tags
       and  |- G ctx     G |- B tags
       and  G prefix of G0 , and B prefix of B0
       and  n + |G| = |G0|
       then sc is a continutation which maps
            |- G' ctx
            and G' |- B' tags
            and G', B' |- w' : G0, B0
            to  |- G'' ctx
            and G'' |- B'' tags
            and G'', B'' extends G, B
       and |- Gnew = G ctx
       and Gnew |- Bnew tags
       where Bnew stems from B where all used lemmas (S.RL) are now tagged with (S.RLdone)
    *)

    fun expand' ((G0, B0), (I.Null, I.Null), n) =
        ((I.Null, I.Null), fn ((G', B'), w') => ((G', B'), w'))
      | expand' ((G0, B0), (I.Decl (G, D as I.Dec (_, V)), I.Decl (B, T as S.Lemma (S.RL))), n) =
        let
          val ((G0', B0'), sc') = expand' ((G0, B0), (G, B), n+1)
          val s = I.Shift (n+1)
          val Vs = Whnf.normalize (V, s)
        in
          case (forward (G0, B0, (Vs)))
            of NONE => ((I.Decl (G0', D), I.Decl (B0', T)), sc')
             | SOME (V') =>
                 ((I.Decl (G0', D), I.Decl (B0', S.Lemma (S.RLdone))),
                  fn ((G', B'), w') =>
                  let


                    val V'' = Whnf.normalize (V', w')
                                        (* G' |- V'' : type *)
                  in
                    sc' ((I.Decl (G', I.Dec (NONE, V'')),
                          I.Decl (B', S.Lemma (S.Splits (!MTPGlobal.maxSplit)))), I.comp (w', I.shift))
                  end)
        end
      | expand' (GB0, (I.Decl (G, D), I.Decl (B, T)), n) =
        let
          val ((G0', B0'), sc') = expand' (GB0, (G, B), n+1)
        in
          ((I.Decl (G0', D), I.Decl (B0', T)), sc')
        end


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else ()
          val ((Gnew, Bnew), sc) = expand' ((G, B), (G, B), 0)
          val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (Gnew) else ()
          val ((G', B'), w') = sc ((Gnew, Bnew), I.id)
          val _ = TypeCheck.typeCheckCtx G'

          val S' = S.State (n, (G', B'), (IH, OH), d, S.orderSub (O, w'),
                   map (fn (i, F') => (i, F.forSub (F', w'))) H, F.forSub (F, w'))
          val _ = if !Global.doubleCheck
                  then FunTypeCheck.isState S'
                  else ()
        in
          fn () => S'
        end


    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
    fun apply f = f ()

    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu _ =  "Inference"

  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
