(* Parsing Define Declarations in Solve Queries *)
(* Author: Roberto Virga *)

signature PARSE_DEFINE =
sig

  structure Parsing   : PARSING
  structure ExtDefine : EXTDEFINE

  val parseDefine' : ExtDefine.define Parsing.parser

end;  (* signature PARSE_DEFINE *)
