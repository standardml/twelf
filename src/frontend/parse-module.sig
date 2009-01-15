(* Parsing modules *)
(* Author: Kevin Watkins *)

signature PARSE_MODULE =
sig
  structure ModExtSyn : MODEXTSYN
  val parseSigBegin' : ModExtSyn.modbegin Parsing.parser
  val parseStrDec' : ModExtSyn.strdec Parsing.parser
  val parseInclude' : ModExtSyn.siginclude Parsing.parser
  val parseOpen' : ModExtSyn.stropen Parsing.parser
end
