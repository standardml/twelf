(* Parsing modules *)
(* Author: Keven Watkins *)
(* Redesigned: Florian Rabe, Jan 09 *)

signature PARSE_MODULE =
sig
  structure ModExtSyn : MODEXTSYN
  val parseSigBegin'  : ModExtSyn.modbegin Parsing.parser
  val parseViewBegin' : ModExtSyn.modbegin Parsing.parser
  val parseRelBegin'  : ModExtSyn.modbegin Parsing.parser
  val parseInclude'   : ModExtSyn.sigincl Parsing.parser
  val parseStrDec'    : ModExtSyn.strdec Parsing.parser
  val parseConInst'   : ModExtSyn.syminst Parsing.parser
  val parseStrInst'   : ModExtSyn.syminst Parsing.parser
  val parseInclInst'  : ModExtSyn.syminst Parsing.parser
  val parseConCase'   : ModExtSyn.symcase Parsing.parser
  val parseInclCase'  : ModExtSyn.symcase Parsing.parser
  val parseStrCase'   : ModExtSyn.symcase Parsing.parser
  val parseRead'      : ModExtSyn.read Parsing.parser
  val parseNamespace' : ModExtSyn.namespace Parsing.parser
end
