(* Meta Abstraction *)
(* Author: Carsten Schuermann *)

signature METAABSTRACT =
sig
  structure MetaSyn : METASYN

  exception Error of string

  val abstract : MetaSyn.State -> MetaSyn.State
end;  (* signature METAABSTRACT *)
