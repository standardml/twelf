(* Data Global parameters *)
(* Author: Carsten Schuermann *)

signature DATA =
sig
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;  (* signature DATA *)
