(* Parsing modules *)
(* Author: Keven Watkins *)
(* Redesigned: Florian Rabe, Jan 09 *)

signature PARSE_MODULE =
sig
  structure ModExtSyn : MODEXTSYN
  val parseSigBegin'  : ModExtSyn.modbegin Parsing.parser
  val parseViewBegin' : ModExtSyn.modbegin Parsing.parser
  val parseStrDec'    : ModExtSyn.strdec Parsing.parser
  val parseConInst'   : ModExtSyn.syminst Parsing.parser
  val parseStrInst'   : ModExtSyn.syminst Parsing.parser
  val parseInclude'   : ModExtSyn.sigincl Parsing.parser
  val parseIncludeView': ModExtSyn.syminst Parsing.parser
  val parseIncludeRel': ModExtSyn.syminst Parsing.parser
  val parseStrRel'    : ModExtSyn.syminst Parsing.parser
  val parseRead'      : ModExtSyn.read Parsing.parser
end
