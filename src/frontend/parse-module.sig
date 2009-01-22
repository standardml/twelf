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
  val parseInclude'   : ModExtSyn.siginclude Parsing.parser
  val parseOpen'      : ModExtSyn.stropen Parsing.parser
end
