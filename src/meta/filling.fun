(* Filling  Version 1.3*)
(* Author: Carsten Schuermann *)

functor MTPFilling (structure MTPGlobal : MTPGLOBAL
                    (*! structure IntSyn : INTSYN !*)
                    (*! structure FunSyn' : FUNSYN !*)
                    (*! sharing FunSyn'.IntSyn = IntSyn !*)
                    structure StateSyn' : STATESYN
                    (*! sharing StateSyn'.FunSyn = FunSyn' !*)
                    structure Abstract : ABSTRACT
                    (*! sharing Abstract.IntSyn = IntSyn !*)
                    structure TypeCheck : TYPECHECK
                    (*! sharing TypeCheck.IntSyn = IntSyn !*)
                    structure MTPData : MTPDATA
                    structure Search   : MTPSEARCH
                      sharing Search.StateSyn = StateSyn'
                    structure Whnf : WHNF
                    (*! sharing Whnf.IntSyn = IntSyn !*)
                      )
  : MTPFILLING =
struct
  (*! structure FunSyn = FunSyn' !*)
  structure StateSyn = StateSyn'

  exception Error of string
  exception TimeOut

  type operator = (unit -> int * FunSyn.Pro)

  local
    structure S = StateSyn
    structure F = FunSyn
    structure I = IntSyn

    exception Success of int

    (* Checking for constraints: Used to be in abstract, now must be done explicitly! --cs*)

    (* createEVars (G, F) = (Xs', P')

       Invariant:
       If   |- G ctx
       and  G |- F = [[x1:A1]] .. [[xn::An]] formula
       then Xs' = (X1', .., Xn') a list of EVars
       and  G |- Xi' : A1 [X1'/x1..X(i-1)'/x(i-1)]          for all i <= n
       and  G; D |- P' = <X1', <.... <Xn', <>> ..> in F     for some D
    *)
    fun createEVars (G, (F.True, s)) = (nil, F.Unit)
      | createEVars (G, (F.Ex (I.Dec (_, V), F), s)) =
        let
          val X = I.newEVar (G, I.EClo (V, s))
          val X' = Whnf.lowerEVar X
          val (Xs, P) = createEVars (G, (F, I.Dot (I.Exp X, s)))
        in
          (X' :: Xs, F.Inx (X, P))
        end


(*    fun checkConstraints nil = raise Success
      | checkConstraints (X :: L) =
        if Abstract.closedExp (I.Null, (Whnf.normalize (X, I.id), I.id)) then checkConstraints L
        else ()
*)

    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S as S.State (n, (G, B), (IH, OH), d, O, H, F)) =
        let
          val _ = if (!Global.doubleCheck) then TypeCheck.typeCheckCtx (G) else ()
          val (Xs, P) = createEVars (G, (F, I.id))
        in
          fn () => ((Search.searchEx (!MTPGlobal.maxFill, Xs, fn max => (if (!Global.doubleCheck) then
                                                       map (fn (X as I.EVar (_, G', V, _)) =>
                                                            TypeCheck.typeCheck (G', (X, V))) Xs
                                                     else []; raise Success max));
                     raise Error "Filling unsuccessful")
                    handle Success max => (MTPData.maxFill := Int.max (!MTPData.maxFill, max);
                                           (max, P)))
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
    fun menu _ =  "Filling   (tries to close this subgoal)"

  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
