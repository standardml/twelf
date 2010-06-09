(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

signature MODEXTSYN =
sig
  structure ExtSyn : EXTSYN

  (* module or symbol level identifier *)
  type id = string list * Paths.region
  (* list of ids to be opened and their new names *)
  type openids = (id * (string * Paths.region)) list
  
  (* morphisms *)
  type morph = id list

  (* symbol (= constant, structure, or inclusion) instantiations *)
  datatype syminst =
     coninst of id * (ExtSyn.term * Paths.region)
   | strinst of id * (morph       * Paths.region)
   | inclinst of morph * Paths.region

  (* logical relation *)
  type rel = id
  (* cases in a logical relations *)
  datatype symcase =
     concase of id * (ExtSyn.term * Paths.region)
   | strcase of id * (rel       * Paths.region)
   | inclcase of rel * Paths.region

  (* inclusion of signatures into signatures and morphisms into link *)  
  datatype sigincl = sigincl of id * openids

  (* structure declarations *)
  datatype strdec = strdec of string * id * (syminst list) * openids * bool
                  | strdef of string * (morph * Paths.region) * bool

  (* begin of a module *)
  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * id * bool
                    | relbegin of string * morph list * Paths.region
  
  (* importing files *)
  datatype read = readfile of string

end;

signature RECON_MODULE =
sig
  include MODEXTSYN
  exception Error of string
  (* reconstructs a morphism, first argument is the codomain mid *)
  val morphToMorph : IDs.mid * (morph * Paths.location) -> ModSyn.Morph
  (* reconstructs an instantiation, first two arguments are domain and codomain mid *)
  val syminstToSymInst : IDs.mid * IDs.mid * syminst * Paths.location -> ModSyn.SymInst
  (* reconstructs a case in a logical relation, first two arguments are domain and codomain mid *)
  val symcaseToSymCase : IDs.mid * IDs.mid * symcase * Paths.location -> ModSyn.SymCase
  (* reconstructs a structure declaration *)
  val strdecToStrDec : strdec * Paths.location -> ModSyn.StrDec
  (* reconstructs the begin of a module declaration *)
  val modbeginToModDec : modbegin * Paths.location -> ModSyn.ModDec
  (* reconstructs a signature inclusion *)
  val siginclToSigIncl : sigincl * Paths.location -> ModSyn.SigIncl
  (* reconstructs a read declaration *)
  val readToRead : read * Paths.location -> ModSyn.Read
end