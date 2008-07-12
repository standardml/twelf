(* Top-Level Parser *)
(* Author: Frank Pfenning *)

signature PARSER =
sig

  (*! structure Parsing : PARSING !*)
  structure Stream : STREAM
  structure ExtSyn : EXTSYN
  structure Names : NAMES
  structure ExtConDec : EXTCONDEC
  structure ExtQuery : EXTQUERY
  structure ExtModes : EXTMODES
  structure ThmExtSyn : THMEXTSYN
  structure ModExtSyn : MODEXTSYN

  datatype fileParseResult =
      ConDec of ExtConDec.condec
    | FixDec of (Names.Qid * Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.Qid * Paths.region) * (string list * string list)
    | ModeDec of ExtModes.modedec list
    | UniqueDec of ExtModes.modedec list (* -fp 8/17/03 *)
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl   (* -bp *)
    | TabledDec of ThmExtSyn.tableddecl 
    | KeepTableDec of ThmExtSyn.keepTabledecl 
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtQuery.query (* expected, try, A *)
    | FQuery of ExtQuery.query (* A *)
    | Compile of Names.Qid list (* -ABP 4/4/03 *)
    | Querytabled of int option * int option * ExtQuery.query        (* expected, try, A *)
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region (* -fp *)
    | SubordDec of (Names.Qid * Names.Qid) list (* -gaw *)
    | FreezeDec of Names.Qid list
    | ThawDec of Names.Qid list
    | DeterministicDec of Names.Qid list  (* -rv *)
    | ClauseDec of ExtConDec.condec (* -fp *)
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig | EndSubsig (* enter/leave a new context *)
    | Use of string
    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> (fileParseResult * Paths.region) Stream.stream
  val parseTerminalQ : string * string -> ExtQuery.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
