(* Global parameters *)
(* Author: Carsten Schuermann *)

signature MTPGLOBAL =
sig
  datatype ProverType = New | Old

  val prover : ProverType ref
  val maxFill : int ref
  val maxSplit : int ref
  val maxRecurse : int ref
end;  (* signature MTPGLOBAL *)
