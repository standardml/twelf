(* Termination checker *)
(* Author: Carsten Schuermann *)

signature TERMINATE =
sig
  structure IntSyn : INTSYN
    
  exception Error of string
    
  val reset : unit -> unit
  val checkFam : IntSyn.cid -> unit 
end;  (* signature TERMINATE *)
