(* Meta Prover *)
(* Author: Carsten Schuermann *)

signature PROVER =
sig
  structure MetaSyn : METASYN

  exception Error of string 

  val init   : (int * MetaSyn.IntSyn.cid list) -> unit
  val auto   : unit -> unit
  val print  : unit -> unit
  val install: (MetaSyn.IntSyn.ConDec -> MetaSyn.IntSyn.cid) -> unit
end;  (* signature PROVER *)
