(* Meta Global parameters *)
(* Author: Carsten Schuermann *)

functor MTPData (structure MTPGlobal : MTPGLOBAL) : MTPDATA =
struct
  val maxFill = ref 0
end; (* structure MTPData*)
