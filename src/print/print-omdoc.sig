(* Printing Signatures to OMDoc *)
(* Author: Florian Rabe *)

signature PRINT_OMDOC =
sig
 val printDoc : string -> unit
 val printModule : (string -> unit) -> IDs.mid -> unit
end;  (* signature PRINT_OMDOC  *)
