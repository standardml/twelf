(* Filling *)
(* Author: Carsten Schuermann *)

signature FILLING = 
sig
  structure MetaSyn : METASYN

  exception Error of string
  exception TimeOut

  type operator

  val expand : MetaSyn.State -> operator list * operator 

  (*
    gets a list of operators, which fill in several non index variables
    on one level simultaneously
  *)

  val apply : operator -> MetaSyn.State list

  (*
    in the case of an induction hypothesis, an operator can transform a
    state into several states. In the case of just filling in the existential
    parameters, there will by only one resulting state (we only need ONE
    witness instantiation of the variables 
  *)

  val menu : operator -> string
end


