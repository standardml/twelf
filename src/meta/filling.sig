(* Filling Version 1.3 *)
(* Author: Carsten Schuermann *)

signature MTPFILLING = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  type operator

  val expand : StateSyn.State -> operator 

  (*
    gets a list of operators, which fill in several non index variables
    on one level simultaneously
  *)
  val apply : operator -> bool

  (*
    in the case of an induction hypothesis, an operator can transform a
    state into several states. In the case of just filling in the existential
    parameters, there will by only one resulting state (we only need ONE
    witness instantiation of the variables 
  *)
  val menu : operator -> string
end


