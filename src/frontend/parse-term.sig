(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_TERM =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseTerm' : ExtSyn.term Parsing.parser
  val parseDec'  : ExtSyn.dec Parsing.parser

end;  (* signature PARSE_TERM *)
