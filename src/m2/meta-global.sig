(* Global parameters *)
(* Author: Carsten Schuermann *)

signature METAGLOBAL =
sig
  datatype Strategy = RFS | FRS

  val strategy : Strategy ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;  (* signature METAGLOBAL *)
