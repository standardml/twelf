(* Printing Signatures to OMDoc *)
(* Author: Florian Rabe *)

signature PRINTFILE =
sig
 (* printDoc NONE outFile: print everything to outFile
    printDoc (SOME fileName) outFile: print declarations from fileName to outFile *)
 val printDoc : string option -> string -> unit
end;  (* signature PRINTFILE  *)
