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
    | FixDec of (ExtSyn.name * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (ExtSyn.name * ExtSyn.Paths.region) * (ExtSyn.name * ExtSyn.name option)
    | ModeDec of ExtModes.modedec (* * ExtSyn.Paths.region *)
    | TerminatesDec of ThmExtSyn.tdecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSynQ.query * ExtSyn.Paths.region (* expected, try, A *)
    | Solve of (ExtSyn.name * ExtSynQ.term) * ExtSyn.Paths.region
    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> fileParseResult Stream.stream
  val parseTerminalQ : string * string -> ExtSynQ.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
