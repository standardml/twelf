(* Compatibility shim from Basis-current to MLton Basis as of 20030716 *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = Array
          structure Vector = Vector
          structure Path = OS.Path
          structure Substring = Substring
	  structure TextIO = CompatTextIO97
	  structure Timer = Timer);
