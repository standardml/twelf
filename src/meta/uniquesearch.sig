(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

signature UNIQUESEARCH = 
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure FunSyn : FUNSYN !*)
  structure StateSyn : STATESYN

  exception Error of string

  type acctype = IntSyn.Exp

  val searchEx : int * IntSyn.Exp list
      * (acctype list -> acctype list) -> acctype list
end;  (* signature SEARCH *)
