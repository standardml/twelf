(* Compatibility shim from Basis-current to SML/NJ Basis as of 110.43 *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = Array
          structure Vector = Vector
          structure Path = OS.Path
          structure Substring = Substring
	  structure Timer = CompatTimer97);
