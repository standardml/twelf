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
    type operator = S.State


    (* expand S = S'

       Invariant:
       If   S = (Psi |>  F)
       and  F does not start with an all quantifier
       then S' = (Psi, xx :: F |> F)
    *)
    fun expand (S.State ((Psi, F), W)) =  
          S.State ((I.Decl (Psi, T.PDec (SOME "IH" , F)),   (* find better name -cs *)
			  T.forSub (F, T.Shift 1)), W)


    (* apply O = S 
     
       Invariant:
       O = S 
    *)
    fun apply S = S


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