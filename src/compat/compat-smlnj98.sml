(* Compatibility shim from Basis-current to SML/NJ Basis as of 110.9.1 *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = CompatArray97
          structure Vector = CompatVector97
          structure Path = OS.Path
	  structure Timer = CompatTimer97);
