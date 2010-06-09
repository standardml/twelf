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
 
  type Qid = IDs.Qid
  
  datatype fileParseResult =
      ConDec of ExtConDec.condec
    | FixDec of (Qid * Paths.region) * Names.Fixity.fixity
    | NamePref of (Qid * Paths.region) * (string list * string list)
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
    | Compile of Qid list (* -ABP 4/4/03 *)
    | Querytabled of int option * int option * ExtQuery.query        (* expected, try, A *)
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region (* -fp *)
    | SubordDec of (Qid * Qid) list (* -gaw *)
    | FreezeDec of Qid list
    | ThawDec of Qid list
    | DeterministicDec of Qid list  (* -rv *)
    | ClauseDec of ExtConDec.condec (* -fp *)
    | Use of string
    | ModBegin of ModExtSyn.modbegin   (* -fr, module system *)
    | ModEnd                           (* -fr, module system *)
    | StrDec of ModExtSyn.strdec       (* -fr, module system *)
    | Include of ModExtSyn.sigincl     (* -fr, module system *)
    | SymInst of ModExtSyn.syminst     (* -fr, module system *)
    | SymCase of ModExtSyn.symcase     (* -fr, logical relations *)
    | Read of ModExtSyn.read           (* -fr, Apr 09 *)

    (* Further declarations to be added here *)

  val parseStream: TextIO.instream -> (fileParseResult * Paths.region) Stream.stream
  val parseTerminalQ : string * string -> ExtQuery.query Stream.stream (* reads from std input *)

end;  (* signature PARSER *)
