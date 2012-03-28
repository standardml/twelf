(* Elim *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:39:26 2006 *)

functor Elim
  (structure Data : DATA
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   (*! sharing Abstract.Tomega = Tomega' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)

       )
     : ELIM =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  datatype Operator =
    Local of Tomega.Prg * int

  type operator = Operator

  local
    structure S = State
    structure T = Tomega
    structure I = IntSyn

    exception Success of int

(* These lines need to move *)

    (* fun stripTC (T.Abs (_, TC)) = TC *)
    fun stripTC TC = TC


    fun stripTCOpt NONE = NONE
      | stripTCOpt (SOME TC) = SOME (stripTC TC)

    fun stripDec (T.UDec D) = T.UDec D
      | stripDec (T.PDec (name, F, TC1, TC2)) = T.PDec (name, F, TC1, stripTCOpt TC2)

    fun strip I.Null = I.Null
      | strip (I.Decl (Psi, D)) = I.Decl (strip Psi, stripDec D)


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' is an operator which performs the filling operation
    *)
    fun expand (S.Focus (Y as T.EVar (Psi, r, G, V, _, _), W)) =   (* Y is lowered *)
      let
        fun matchCtx (I.Null, _, Fs) = Fs
          | matchCtx (I.Decl (G, T.PDec (x, F, _, _)), n, Fs) =
          matchCtx (G, n+1, Local (Y, n) :: Fs)
          | matchCtx (I.Decl (G, T.UDec _), n, Fs) =
          matchCtx (G, n+1, Fs)

      in
        matchCtx (Psi, 1, nil)
      end

    (* apply op = B'

       Invariant:
       If op is a filling operator
       then B' holds iff the filling operation was successful
    *)
   fun apply (Local (R as T.EVar (Psi, r, G, NONE, NONE, _), n)) =
       let
         val T.PDec (_, F0, _, _) = T.ctxDec (Psi, n)
       in
         (case F0
            of T.All ((T.UDec (I.Dec (_, V)), _), F) =>
             let
               val X = I.newEVar (T.coerceCtx (strip Psi), V)
               val I.NDec x = Names.decName (T.coerceCtx Psi, I.NDec NONE)
               val D = T.PDec (x, T.forSub (F, T.Dot (T.Exp X, T.id)), NONE, NONE)
               (* the NONE, NONE may breach an invariant *)
               (* revisit when we add subterm orderings *)
               val Psi' = I.Decl (Psi, D)
               val Y = T.newEVar (strip Psi', T.forSub (G, T.shift))
             in
               (r := SOME (T.Let (D, T.Redex (T.Var n, T.AppExp (X, T.Nil)), Y)))
             end
         | T.Ex ((D1, _), F) =>
             let
               val D1' = Names.decName (T.coerceCtx Psi, D1)
               val Psi' = I.Decl (Psi, T.UDec D1')
               val I.NDec x = Names.decName (T.coerceCtx (Psi'), I.NDec NONE)
               val D2 = T.PDec (x, F, NONE, NONE)
               val Psi'' = I.Decl (Psi', D2)
               val Y = T.newEVar (strip Psi'', T.forSub (G, T.Shift 2))
             in
               (r := SOME (T.LetPairExp (D1', D2, T.Var n, Y)))
             end
         | T.True =>
             let
               val Y = T.newEVar (strip Psi, G)
             in
               (r := SOME (T.LetUnit (T.Var n, Y)))
             end)
       end
      | apply (Local (T.EVar (Psi, r, T.FClo (F, s), TC1, TC2, X), n)) =
           apply (Local (T.EVar (Psi, r, T.forSub (F, s), TC1, TC2, X), n))


    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu (Local (X as T.EVar (Psi, _, _, _, _, _), n)) =
        (case (I.ctxLookup (Psi, n))
          of T.PDec (SOME x, _, _, _) =>
            ("Elim " ^ TomegaPrint.nameEVar X  ^ " with variable " ^ x))
           (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)

  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor elim *)
