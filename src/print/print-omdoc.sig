(* Printing Signatures to OMDoc *)
(* Author: Florian Rabe *)

signature PRINT_OMDOC =
sig
 (* argument: file name *)
 val printDoc : string -> unit
 (* arguments: print, flush, module id *)
 val printModule : (string -> unit) -> (unit -> unit) -> IDs.mid -> unit
end;  (* signature PRINT_OMDOC  *)
