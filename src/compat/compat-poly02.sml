(* Compatibility shim from Basis-current to Poly/ML Basis as of 4.1.3 *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = CompatArray97
          structure Vector = CompatVector97
          structure Path = OS.Path
	  structure Substring = CompatSubstring97
          structure TextIO = CompatTextIO97
	  structure Timer = Timer);
