(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

signature MTPSEARCH = 
sig
  structure StateSyn : STATESYN

  exception Error of string

  val searchEx : 
      StateSyn.FunSyn.IntSyn.dctx * StateSyn.FunSyn.IntSyn.Exp list
(*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
      * (unit -> unit) -> unit
end;  (* signature SEARCH *)
