(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

signature STRICT =
sig
  structure IntSyn : INTSYN
  structure Paths : PATHS

  exception Error of string
  
  val check : IntSyn.ConDec * Paths.occConDec option -> unit 
end;  (* signature STRICT *)
