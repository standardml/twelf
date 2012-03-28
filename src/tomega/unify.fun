(* Unification on Formulas *)
(* Author: Carsten Schuermann *)

functor TomegaUnify
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure TypeCheck : TYPECHECK
   (*! sharing TypeCheck.IntSyn = IntSyn' !*)
   structure Conv : CONV
   (*! sharing Conv.IntSyn = IntSyn' !*)
   structure Normalize : NORMALIZE
   (*! sharing Normalize.IntSyn = IntSyn' !*)
   (*! sharing Normalize.Tomega = Tomega' !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
   structure Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
       ) : TOMEGAUNIFY =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)

  exception Unify of string

  local
    structure I = IntSyn
    structure T = Tomega

    (* unifyFor (Psi, F1, F2) = R

       Invariant:
       If   F1, F2 contain free variables X1 ... Xn
       and  Psi |- F1 for
       and  Psi |- F2 for
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- F1[I] = F2[I]
       then R = ()
       otherwise exception Unify is raised
    *)

    fun unifyFor (Psi, F1, F2) =
          unifyForN (Psi,
                     T.forSub (F1, T.id),
                     T.forSub (F2, T.id))
    and unifyForN (Psi, T.True, T.True) = ()
      | unifyForN (Psi, T.Ex ((D1, _), F1), T.Ex ((D2, _), F2)) =
        (unifyDec (Psi, T.UDec D1, (T.UDec D2));
         unifyFor(I.Decl (Psi, T.UDec D1), F1, F2))
      | unifyForN (Psi, T.All ((D1, _), F1), T.All ((D2, _), F2)) =
        (unifyDec (Psi, D1, D2);
         unifyFor(I.Decl (Psi, D1), F1, F2))
      | unifyForN (Psi, T.FVar (_, r), F) =
        (r := SOME F)
      | unifyForN (Psi, F, T.FVar (_, r)) =
        (r := SOME F)
      | unifyForN (Psi, _, _) = raise Unify "Formula mismatch"


    (* unifyDec (Psi, D1, D2) = R

       Invariant:
       If   D1, D2 contain free variables X1 ... Xn
       and  Psi |- D1 dec
       and  Psi |- D2 dec
       and  there exists an instantiation I for X1 ...Xn such that
       and  Psi[I] |- D1[I] = D2[I]
       then R = ()
       otherwise exception Unify is raised
    *)
    and unifyDec (Psi, T.UDec D1, T.UDec D2) =
          if Conv.convDec ((D1, I.id), (D2, I.id)) then ()
          else raise Unify "Declaration mismatch"
      | unifyDec (Psi, T.PDec (_, F1), T.PDec (_, F2)) =
          unifyFor (Psi, F1, F2)



  in
    val unifyFor = unifyFor
  end
end
