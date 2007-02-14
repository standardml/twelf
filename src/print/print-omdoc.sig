(* Printing Signatures to OMDoc*)
(* Author: Florian Rabe *)

signature PRINT_OMDOC =
sig
 (* printSgn F n exports the current signature as an OMDoc document to the file with path F. If n is true, all constant and variable names are replaced to guarantee uniqueness of names. Otherwise, the user has to make sure that no overloading is used. *)
 val printSgn : string -> bool -> unit
 (* printConst c prints the OMDoc fragment (without name safety) for the constant with cid c. *)
 val printConst : IntSyn.cid -> string
end;  (* signature PRINT_XML *)
