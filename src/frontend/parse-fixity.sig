(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_FIXITY =
sig

  (*! structure Parsing : PARSING !*)
  structure Names : NAMES

  val parseFixity' : ((string list * Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((string list * Paths.region)
			* (string list * string list)) Parsing.parser

end;  (* signature PARSE_FIXITY *)
