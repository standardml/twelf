(* Filling *)
(* Author: Carsten Schuermann *)
(* Date: Thu Mar 16 13:08:33 2006 *)

functor Fill
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
   structure Search  : SEARCH
   (*! sharing Search.IntSyn = IntSyn' !*)
   (*! sharing Search.Tomega = Tomega' !*)
     sharing Search.State = State'
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn' !*)

       )
     : FILL =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error of string

  datatype Operator =
    FillWithConst of IntSyn.Exp * IntSyn.cid
       (* Representation Invariant:  FillWithConst (X, c) :
           X is an evar GX |- X : VX
           Sigma |- c : W
           and VX and W are unifiable
       *)
    | FillWithBVar of IntSyn.Exp * int
       (* Representation Invariant:  FillWithBVar (X, n) :
           X is an evar GX |- X : VX
           GX |- n : W
           and VX and W are unifiable
       *)

  type operator = Operator

  local
    structure S = State
    structure T = Tomega
    structure I = IntSyn

    exception Success of int


    (* expand' S = op'

       Invariant:
       If   |- S state
       then op' satifies representation invariant.
    *)
    fun expand (S.FocusLF (Y as I.EVar (r, G, V, _))) =   (* Y is lowered *)
      let
        fun try (Vs as (I.Root _, _), Fs, O) =
          (CSManager.trail (fn () => (Unify.unify (G, Vs, (V, I.id)); O :: Fs))
           handle Unify.Unify _ => Fs)
          | try ((I.Pi ((I.Dec (_, V1), _), V2), s), Fs, O) =
          let
            val X = I.newEVar (G, I.EClo (V1, s))
          in
            try ((V2, I.Dot (I.Exp X, s)), Fs, O)
          end
          | try ((I.EClo (V, s'), s), Fs, O) = try ((V, I.comp (s', s)), Fs, O)

        (* matchCtx (G, n, Fs) = Fs'

           Invariant:
           If G0 = G, G' and |G'| = n and Fs a list of filling operators that
           satisfy the representation invariant, then Fs' is a list of filling operators
           that satisfy the representation invariant.
        *)
        fun matchCtx (I.Null, _, Fs) = Fs
          | matchCtx (I.Decl (G, I.Dec (x, V)), n, Fs) =
          matchCtx (G, n+1, try ((V, I.Shift (n+1)), Fs, FillWithBVar (Y, n+1)))
          | matchCtx (I.Decl (G, I.NDec _), n, Fs) =
          matchCtx (G, n+1, Fs)

        fun matchSig (nil, Fs) = Fs
          | matchSig (I.Const (c)::L, Fs) =
          matchSig (L, try ((I.constType (c), I.id), Fs, FillWithConst (Y, c)))
      in
        matchCtx (G, 0, matchSig (Index.lookup (I.targetFam V), nil))
      end

    (* apply op = ()

       Invariant:
       If op is a filling operator that satisfies the representation invariant.
       The apply operation is guaranteed to always succeed.
    *)
    fun apply (FillWithBVar(Y as I.EVar (r, G, V, _), n)) = (* Y is lowered *)
      let
        (* Invariant : G |- s : G'   G' |- V : type *)
        fun doit (Vs as (I.Root _, _),  k) =
            (Unify.unify (G, Vs, (V, I.id)); (k I.Nil))  (* Unify must succeed *)
          | doit ((I.Pi ((I.Dec (_, V1), _), V2), s), k) =
            let
              val X = I.newEVar (G, I.EClo (V1, s))
            in
              doit ((V2, I.Dot (I.Exp X, s)),  (fn S => k (I.App (X, S))))
            end
          | doit ((I.EClo (V, t), s), k) = doit ((V, I.comp (t, s)), k)

        val I.Dec (_, W) = I.ctxDec (G, n)
      in
        doit ((W, I.id),  fn S => Unify.unify (G, (Y, I.id), (I.Root (I.BVar n, S), I.id)))
      end
    | apply (FillWithConst(Y as I.EVar (r, G0, V, _), c)) =
      let
        fun doit (Vs as (I.Root _, _),  k) =
            (Unify.unify (G0, Vs, (V, I.id)); (k I.Nil))  (* Unify must succeed *)
          | doit ((I.Pi ((I.Dec (_, V1), _), V2), s), k) =
            let
              val X = I.newEVar (G0, I.EClo (V1, s))
            in
              doit ((V2, I.Dot (I.Exp X, s)),  (fn S => k (I.App (X, S))))
            end
        val W = I.constType c
      in
        doit ((W, I.id),  fn S => Unify.unify (G0, (Y, I.id), (I.Root (I.Const c, S), I.id)))
      end

    (* menu op = s'

       Invariant:
       If op is a filling operator
       then s' is a string describing the operation in plain text
    *)
    fun menu (FillWithBVar (X as I.EVar (_, G, _, _), n)) =
        (case (I.ctxLookup (Names.ctxName G, n))
          of I.Dec (SOME x, _) =>
            ("Fill " ^ Names.evarName (G, X) ^ " with variable " ^ x))
           (* Invariant: Context is named  --cs Fri Mar  3 14:31:08 2006 *)
      | menu (FillWithConst (X as I.EVar (_, G, _, _), c)) =
           ("Fill " ^ Names.evarName (G, X) ^ " with constant " ^ IntSyn.conDecName (IntSyn.sgnLookup c))

  in
    val expand = expand
    val apply = apply
    val menu = menu
  end (* local *)
end; (* functor Filling *)
