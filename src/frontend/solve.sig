(* Solve and query declarations, interactive top level *)
(* Author: Frank Pfenning *)

signature SOLVE =
sig

  structure IntSyn : INTSYN
  structure ExtSyn : EXTSYN
  structure Paths : PATHS

  exception AbortQuery of string

  val solve : (string * ExtSyn.term) * Paths.location -> IntSyn.ConDec

  val query : (int option * int option * ExtSyn.query) * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

  val querytabled : (int option * ExtSyn.query) * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

  val qLoop : unit -> bool		(* true means normal exit *)

end;  (* signature SOLVE *)
