(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* morphisms *)
  type morph = (string list * Paths.region) list

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
  (* reconstructs a morphism, first argument is the codomain mid *)
  val morphToMorph : IDs.mid * (morph * Paths.location) -> ModSyn.Morph
  (* reconstructs an instantiation, first two arguments are domain and codomain mid *)
  val syminstToSymInst : IDs.mid * IDs.mid * syminst * Paths.location -> ModSyn.SymInst
  (* reconstructs a structure declaration *)
  val strdecToStrDec : strdec * Paths.location -> ModSyn.StrDec
  (* reconstructs the begin of a module declaration *)
  val modbeginToModDec : modbegin -> ModSyn.ModDec
end