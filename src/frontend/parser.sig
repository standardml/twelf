(* Top-Level Parser *)
(* Author: Frank Pfenning *)

signature PARSER =
sig

  structure Parsing : PARSING
  structure Stream : STREAM
  structure ExtSyn : EXTSYN		(* Free variables are universal *)
  structure ExtSynQ : EXTSYN		(* Free variables are existential *)
  structure Names : NAMES
  structure ExtModes : EXTMODES
  structure ThmExtSyn : THMEXTSYN

  datatype fileParseResult =
      ConDec of ExtSyn.condec * ExtSyn.Paths.region
    | FixDec of (string * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (string * ExtSyn.Paths.region) * (string * string option)
    | ModeDec of ExtModes.modedec (* * ExtSyn.Paths.region *)
    | TerminatesDec of ThmExtSyn.tdecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSynQ.query * ExtSyn.Paths.region (* expected, try, A *)
    | Solve of (string * ExtSynQ.term) * ExtSyn.Paths.region
    | AbbrevDec of ExtSyn.condec * ExtSyn.Paths.region
    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> fileParseResult Stream.stream
  val parseTerminalQ : string * string -> ExtSynQ.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
