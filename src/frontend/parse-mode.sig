(* Parsing Mode Declarations *)
(* Author: Carsten Schuermann *)

signature PARSE_MODE =
sig

  (*! structure Parsing : PARSING !*)
  structure ExtModes: EXTMODES

  val parseMode' : (ExtModes.modedec list) Parsing.parser

end;  (* signature PARSE_MODE *)
