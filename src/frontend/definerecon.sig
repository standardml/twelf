(* External Syntax of Define Statements in Solve Queries *)
(* Author: Roberto Virga *)

signature EXTDEFINE =
sig
  structure ExtSyn : EXTSYN
  structure Paths : PATHS

  type define

  val define : string * ExtSyn.term option * string * Paths.region -> define
end;  (* signature EXTDEFINE *)


signature DEFINE_RECON =
sig
  include EXTDEFINE
  structure IntSyn : INTSYN

  datatype Define =
    Define of string * IntSyn.Exp option * string

  exception Error of string
  val error : Paths.region * string -> unit

  val defineToDefine : define -> Define * Paths.region
end;  (* signature DEFINE_RECON *)
