(* Compatibility shim from Basis-current to Basis-97 *)
(* Author: Christopher Richards *)

structure Compat :> COMPAT =
  Compat (structure Array = CompatArray97
          structure Vector = CompatVector97
          structure Path = CompatPath97
	  structure Substring = CompatSubstring97
	  structure TextIO = CompatTextIO97
	  structure Timer = CompatTimer97
	  structure SocketIO = CompatSocketIO97);
