(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_TERM =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseQualId' : (string list * Parsing.lexResult) Parsing.parser
  val parseTerm' : ExtSyn.term Parsing.parser
  val parseDec'  : (string option * ExtSyn.term option) Parsing.parser

end;  (* signature PARSE_TERM *)
