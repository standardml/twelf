(* Basic search engine: Version 1.3*)
(* Author: Carsten Schuermann *)

signature SEARCH = 
sig
  (*! structure IntSyn   : INTSYN !*)
  (*! structure Tomega   : TOMEGA !*)
  structure State    : STATE

  exception Error of string

  val searchEx : int * IntSyn.Exp list
(*      * (StateSyn.FunSyn.IntSyn.Exp * StateSyn.FunSyn.IntSyn.Sub) *)
      * (int -> unit) -> unit
end;  (* signature SEARCH *)
