(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

signature PARSE_CONDEC =
sig

  structure Parsing : PARSING
  structure ExtSyn : EXTSYN

  val parseConDec' : ExtSyn.condec Parsing.parser

end;  (* signature PARSE_CONDEC *)
