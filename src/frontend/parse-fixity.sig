(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_FIXITY =
sig

  (*! structure Parsing : PARSING !*)
  structure Names : NAMES

  val parseFixity' : ((Names.Qid * Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((Names.Qid * Paths.region)
			* (string * string option)) Parsing.parser

end;  (* signature PARSE_FIXITY *)
