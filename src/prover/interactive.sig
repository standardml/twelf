(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

signature INTERACTIVE =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)
  structure State  : STATE

  exception Error of string 
  
  val init   : string list -> unit
  val select : int -> unit 
  val print  : unit -> unit
  val stats  : unit -> unit
  val focus  : string -> unit
  val return : unit -> unit
(*   val next   : unit -> unit *)

  val reset  : unit -> unit
(*  val undo   : unit -> unit *)
end;  (* signature Interactive *)


