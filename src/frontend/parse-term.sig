(* Parsing Terms and Declarations *)
(* Author: Frank Pfenning *)

signature PARSE_TERM =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseQualId' : (string list * Parsing.lexResult) Parsing.parser
  val parseQualIds' : ((string list * string) list) Parsing.parser 
  val parseFreeze' : ((string list * string) list) Parsing.parser
  val parseTerm' : ExtSyn.term Parsing.parser
  val parseDec' : (string option * ExtSyn.term option) Parsing.parser
  val parseCtx' : (ExtSyn.dec list) Parsing.parser

end;  (* signature PARSE_TERM *)
