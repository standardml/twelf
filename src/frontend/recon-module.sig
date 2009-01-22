(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* morphisms *)
  datatype morph = (string list * Paths.region) list

  (* symbol (= constant or structure) instantiations *)
  datatype syminst =
     coninst of (string list * Paths.region) * (ExtSyn.term * Paths.region)
   | strinst of (string list * Paths.region) * (morph       * Paths.region)

  (* structure declarations *)
  datatype strdec = strdec of string * (string list * Paths.region) * (syminst list)
                  | strdef of string * (morph * Paths.region)

  (* begin of a module *)
  datatype modbegin = sigbegin of string
                    | viewbegin of string * (string list * Paths.region) * (string list * Paths.region)
  
  (* include and open currently not supported *)
  type siginclude = unit
  type stropen = unit
end;

signature RECON_MODULE =
sig
  include MODEXTSYN
  exception Error of string
  val morphToMorph : IDs.mid * IDs.mid * (morph * Paths.location) -> ModSyn.Morph
  val syminstToSymInst : IDs.mid * IDs.mid * syminst * Paths.location -> ModSyn.SymInst
  val strdecToStrDec : IDs.mid * strdec * Paths.location -> ModSyn.StrDec
  val modbeginToModDec : modbegin -> ModSyn.ModDec
end