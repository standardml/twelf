(* Parsing modules *)
(* Author: Kevin Watkins *)

signature PARSE_MODULE =
sig

  (*! structure Parsing : PARSING !*)
  structure ModExtSyn : MODEXTSYN

  (* val parseSigExp' : ModExtSyn.sigexp Parsing.recparser *)
  val parseSigDef' : ModExtSyn.sigdef Parsing.recparser
  (* val parseStructExp' : ModExtSyn.strexp Parsing.parser *)
  val parseStructDec' : ModExtSyn.structdec Parsing.recparser
  val parseInclude' : ModExtSyn.sigexp Parsing.recparser
  val parseOpen' : ModExtSyn.strexp Parsing.parser

end
