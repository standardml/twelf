(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

signature MPI =
sig
  structure MetaSyn : METASYN

  exception Error of string 

  val init   : (int * string list) -> unit
  val select : int -> unit 
  val print  : unit -> unit
  val next   : unit -> unit
  val auto   : unit -> unit
  val solve  : unit -> unit
  val lemma  : string -> unit

  val reset  : unit -> unit
  val extract: unit -> MetaSyn.Sgn
  val show   : unit -> unit
  val undo   : unit -> unit 
end;  (* signature MPI *)


