(* Compatibility shim from Basis-current to itself *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = Array
          structure Vector = Vector
          structure Path = OS.Path
	  structure Timer = Timer);
