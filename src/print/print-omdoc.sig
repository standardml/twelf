(* Printing Signatures to OMDoc *)
(* Author: Florian Rabe *)

signature PRINTFILE =
sig
 (* argument: file name *)
 val toFile : string -> unit
end;  (* signature PRINTFILE  *)
