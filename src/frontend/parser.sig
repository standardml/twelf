(* Top-Level Parser *)
(* Author: Frank Pfenning *)

signature PARSER =
sig

  structure Parsing : PARSING
  structure Stream : STREAM
  structure ExtSyn : EXTSYN
  structure Names : NAMES
  structure ExtModes : EXTMODES
  structure ThmExtSyn : THMEXTSYN

  datatype fileParseResult =
      ConDec of ExtSyn.condec * ExtSyn.Paths.region
    | FixDec of (string * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (string * ExtSyn.Paths.region) * (string * string option)
    | ModeDec of ExtModes.modedec list (* * ExtSyn.Paths.region *)
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl   (* -bp *)
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSyn.query * ExtSyn.Paths.region (* expected, try, A *)
    | Solve of (string * ExtSyn.term) * ExtSyn.Paths.region
    | AbbrevDec of ExtSyn.condec * ExtSyn.Paths.region
    | Use of string
    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> fileParseResult Stream.stream
  val parseTerminalQ : string * string -> ExtSyn.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
