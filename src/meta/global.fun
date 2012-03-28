(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor MTPGlobal
  (structure MetaGlobal : METAGLOBAL): MTPGLOBAL =
struct
  datatype ProverType = New | Old

  val prover = ref New
  val maxFill = MetaGlobal.maxFill
  val maxSplit = MetaGlobal.maxSplit
  val maxRecurse = MetaGlobal.maxRecurse
end; (* structure MTPGlobal *)
