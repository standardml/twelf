(* Introduce *)
(* Author: Carsten Schuermann *)

functor Introduce 
  ((*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
       ) : INTRODUCE  =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  local 
  structure S = State'
  structure T = Tomega
  structure I = IntSyn

    exception Error = S.Error
    type operator = S.State

    (* introduce (Psi, F) = (Psi', F')

       Invariant:
       If   Psi is a meta context
       and  F = all x1:A1 .... xn: An. F1)
       and  F1 does not start with an all quantifier
       then Psi' = Psi, x1:A1, ... xn:An
       and  F' = F1 
    *)

    fun introduce (Psi, T.All ((D, _), F)) = introduce (I.Decl (Psi, D), F)
      | introduce PsiF = PsiF

    (* expand S = S'

       Invariant:
       If   S = (Psi |> all x1:A1 .... xn: An. F)
       and  F does not start with an all quantifier
       then S' = (Psi, x1:A1, ... xn:An |> F)
    *)
    fun expand (S.State ((Psi, F as T.All _), W)) =  SOME (S.State (introduce (Psi, F), W))
      | expand _ = NONE


    (* apply O = S 
     
       Invariant:
       O = S 
    *)
    fun apply S = S


    (* menu O = s 

       Invariant:
       s = "Apply universal introduction rules"
    *)
    fun menu _ = "Intro"
      

  in
    exception Error = Error
    type operator = operator
      
    val expand = expand
    val apply = apply
    val menu =menu
  end
end