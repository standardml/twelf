(* Checking Definitions for Strictness *)
(* Author: Carsten Schuermann *)

signature STRICT =
sig
  structure IntSyn : INTSYN
  structure Paths : PATHS

  exception Error of string
  
  val check : (IntSyn.Exp * IntSyn.Exp) * Paths.occConDec option -> bool 
end;  (* signature STRICT *)
