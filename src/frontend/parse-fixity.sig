(* Parsing Fixity Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_FIXITY =
sig

  structure Parsing : PARSING
  structure Names : NAMES

  val parseFixity' : ((string * Parsing.Lexer.Paths.region) * Names.Fixity.fixity) Parsing.parser
  val parseNamePref' : ((string * Parsing.Lexer.Paths.region)
			* (string * string option)) Parsing.parser

end;  (* signature PARSE_FIXITY *)
