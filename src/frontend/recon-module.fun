(* Elaboration for module expressions *)
(* Author: Florian Rabe *)

functor ReconModule
  (structure Global : GLOBAL
   structure Names : NAMES
   structure ReconTerm' : RECON_TERM
   structure ModSyn' : MODSYN
   structure IntTree : TABLE where type key = int)
  : RECON_MODULE =
struct

(* implementing the signature MODEXTSYN *)
  structure ExtSyn = ReconTerm'

  datatype morph = morstr of string list * string * Paths.region
  datatype syminst =
     coninst of (string list * string * Paths.region) * (ExtSyn.term * Paths.region)
   | strinst of (string list * string * Paths.region) * (morph       * Paths.region)

  datatype strdec = strdec of string * (string * Paths.region) * (syminst list)

  datatype modbegin = sigbegin of string
  datatype modend = sigend
(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string

  (* local function to throw an exception *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  fun morphToMorph(mor, Paths.Loc (fileName, r)) = error (r, "not implemented yet")
  
  fun syminstToSymInst(inst, Paths.Loc (fileName, r)) = error (r, "not implemented yet")
  
  fun strdecToStrDec(strdec(name, domainr, insts), Paths.Loc (fileName, r)) = error (r, "not implemented yet")

end
