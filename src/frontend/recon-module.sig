(* External syntax for module expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* morphisms *)
  type morph
  val morstr : string list * string * Paths.region -> morph

  (* symbol (= constant or structure) instantiations *)
  type syminst
  val coninst : (string list * string * Paths.region) * (ExtSyn.term * Paths.region) -> syminst
  val strinst : (string list * string * Paths.region) * (morph       * Paths.region) -> syminst

  (* structure declarations *)
  type strdec
  val strdec : string * (string list * Paths.region) * (syminst list) -> strdec
  val strdef : string * (morph * Paths.region) -> strdec

  (* begin and end of a module *)
  type modbegin
  val sigbegin : string -> modbegin
  
  type siginclude = unit
  type stropen = unit
end;

signature RECON_MODULE =
sig
  include MODEXTSYN
  exception Error of string
  val morphToMorph : morph * Paths.location -> ModSyn.Morph
  val syminstToSymInst : syminst * Paths.location -> ModSyn.SymInst
  val strdecToStrDec : strdec * Paths.location -> ModSyn.StrDec
end