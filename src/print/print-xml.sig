(* Printing Signatures *)
(* Author: Frank Pfenning *)
(* modified: Carsten Schuermann *)

signature PRINT_XML =
sig
  val printSgn : unit -> unit
  val printSgnToFile : string -> string -> unit
end;  (* signature PRINT_XML *)
