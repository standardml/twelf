(* Operational semantics *)
(* Author: Carsten Schuermann *)

signature Interpreter = 
sig
  (*! structure FunSyn : FUNSYN !*)

  val run : FunSyn.Pro -> FunSyn.Pro
end (* Signature Interpreter *)       
