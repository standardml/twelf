(* Parsing LFR Declarations *) 
(* Author: William Lovas *)

signature PARSE_LFRDEC =
sig

  structure ExtLFRDec : EXTLFRDEC

  val parseLFRDec' : ExtLFRDec.lfrdec Parsing.parser

end;  (* signature PARSE_LFRDEC *)
