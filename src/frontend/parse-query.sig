(* Parsing Queries *) 
(* Author: Frank Pfenning *)

signature PARSE_QUERY =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseQuery' : ExtSyn.query Parsing.parser

end;  (* signature PARSE_QUERY *)
