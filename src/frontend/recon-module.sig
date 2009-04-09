(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* module or symbol level identifier *)
  type id = string list * Paths.region
  (* list of ids to be opened *)
  type openids = id list
  
  (* morphisms *)
  type morph = id list

  (* symbol (= constant or structure) instantiations *)
  datatype syminst =
     coninst of id * (ExtSyn.term * Paths.region)
   | strinst of id * (morph       * Paths.region)

  (* inclusion of signatures into signatures and morphisms into link *)  
  datatype modincl = sigincl of id * openids
                   | viewincl of morph * Paths.region

  (* structure declarations *)
  datatype strdec = strdec of string * id * (modincl list) * (syminst list) * openids
                  | strdef of string * (morph * Paths.region)

  (* begin of a module *)
  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * id

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
  (* reconstructs a module inclusion *)
  val modinclToModIncl : modincl -> ModSyn.ModIncl
end