(* Fixed Point *)
(* Author: Carsten Schuermann *)

functor FixedPoint
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
       ) : FIXEDPOINT  =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  local
  structure S = State'
  structure T = Tomega
  structure I = IntSyn

    exception Error = S.Error
    type operator = (T.Prg option ref * T.Prg)


    (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
    fun expand (S.Focus (T.EVar (Psi, r, F, _, TCs, _), W), O) =
        let
(*        val D = T.PDec (SOME "IH" , F, SOME O, SOME O) *)
          val I.NDec x = Names.decName (T.coerceCtx Psi, I.NDec NONE)
          val D = T.PDec (x, F, NONE, NONE)
          val X = T.newEVar (I.Decl (Psi, D), T.forSub (F, T.Shift 1))
        in
          (r, T.Rec (D, X))
        end

    (* apply O = S

       Invariant:
       O = S
    *)
    fun apply (r, P) = (r := SOME P)   (* should be trailed -cs Thu Apr 22 11:20:32 2004 *)

    (* menu O = s

       Invariant:
       s = "Apply universal introduction rules"
    *)
    fun menu _ = "Recursion introduction"


  in
    exception Error = Error
    type operator = operator

    val expand = expand
    val apply = apply
    val menu =menu
  end
end