(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

signature FQUERY =
sig
  structure ExtQuery : EXTQUERY

  exception AbortQuery of string

  val run : ExtQuery.query * Paths.location -> unit
					(* may raise AbortQuery(msg) *)

end;  (* signature SOLVE *)
