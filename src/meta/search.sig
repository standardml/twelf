(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

signature MTPSEARCH = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  val searchEx : int * IntSyn.Exp list
(*      * (IntSyn.Exp * IntSyn.Sub) *)
      * (int -> unit) -> unit
end;  (* signature SEARCH *)
