(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)

signature SOLVE =
sig

  structure IntSyn : INTSYN
  structure ExtSynQ : EXTSYN
  structure Paths : PATHS

  exception AbortQuery of string

  val solve : (string * ExtSynQ.term) * Paths.location -> IntSyn.ConDec

  val query : (int option * int option * ExtSynQ.query) * Paths.location -> unit
					(* may raise AbortQuery(msg) *)
  val qLoop : unit -> bool		(* true means normal exit *)

end;  (* signature SOLVE *)
