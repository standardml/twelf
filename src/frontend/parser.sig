(* Top-Level Parser *)
(* Author: Frank Pfenning *)

signature PARSER =
sig

  structure Parsing : PARSING
  structure Stream : STREAM
  structure ExtSyn : EXTSYN
  structure Names : NAMES
  structure ExtDefine : EXTDEFINE
  structure ExtModes : EXTMODES
  structure ThmExtSyn : THMEXTSYN
  structure ModExtSyn : MODEXTSYN

  datatype fileParseResult =
      ConDec of ExtSyn.condec
    | FixDec of (Names.Qid * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.Qid * ExtSyn.Paths.region) * (string * string option)
    | ModeDec of ExtModes.modedec list
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl   (* -bp *)
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSyn.query (* expected, try, A *)
    | Querytabled of int option * ExtSyn.query        (* expected, try, A *)
    | Solve of  ExtDefine.define list * string option * ExtSyn.term
    | AbbrevDec of ExtSyn.condec
    | FreezeDec of Names.Qid list
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig | EndSubsig (* enter/leave a new context *)
    | Use of string
    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> (fileParseResult * ExtSyn.Paths.region) Stream.stream
  val parseTerminalQ : string * string -> ExtSyn.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
