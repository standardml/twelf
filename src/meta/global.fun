(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

structure MTPGlobal : MTPGLOBAL =
struct
  val maxFill = ref 6
  val maxSplit = ref 2
  val maxRecurse = ref 10
end; (* structure MTPGlobal *)
