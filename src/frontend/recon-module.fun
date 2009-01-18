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

  datatype morph = morstr of (string list * string * Paths.region)
  datatype syminst =
     coninst of (string list * string * Paths.region) * (ExtSyn.term * Paths.region)
   | strinst of (string list * string * Paths.region) * (morph       * Paths.region)

  datatype strdec = strdec of string * (string list * Paths.region) * (syminst list)
                  | strdef of string * (morph * Paths.region)

  datatype modbegin = sigbegin of string
  
  type siginclude = unit
  type stropen = unit
(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string

  (* local functions to handle errors *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))
  
  fun nameLookupWithError(m : IDs.mid, l : IDs.Qid, r : Paths.region) =
     case Names.nameLookup (m,l)
       of SOME c => c
        | NONE => error(r, "undeclared identifier")

  fun modnameLookupWithError(l : string list, r : Paths.region) =
     case Names.modnameLookup l
       of SOME c => c
        | NONE => error(r, "undeclared module identifier")

(* @CS: is all the paths stuff right in the sequel *)
  fun morphToMorph(Dom : IDs.mid, Cod : IDs.mid, (mor, r)) =
     case mor
       of morstr(names, name, r) =>
          let
             val Str = nameLookupWithError(Cod, names @ [name], r)
          in
             ModSyn.MorStr Str
          end
  
  fun syminstToSymInst(Dom : IDs.mid, Cod : IDs.mid, inst : syminst, l as Paths.Loc (fileName, r)) =
     case inst
        of coninst(con as (names, name, r), term) =>
             let
             	val Con = nameLookupWithError(Dom, names @ [name], r)
             	val Term = error(r, "not implemented yet") (* @CS: I want to call something like ExtSyn.termToTerm(term, l) *)
             in
             	ModSyn.ConInst(Con, Term)
             end
        
         | strinst(str as (names, name, r), mor) =>
             let
             	val Str = nameLookupWithError(Dom, names @ [name], r)
             	val Mor = morphToMorph (Dom, Cod, mor)
             in
             	ModSyn.StrInst(Str, Mor)
             end
  
  fun strdecToStrDec(Cod : IDs.mid, strdec(name : string, (dom : string list, r1 : Paths.region), insts : syminst list),
                     l as Paths.Loc (fileName, r2)
  ) = 
    let
    	val Dom : IDs.mid = modnameLookupWithError(dom, r1)
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,l)) insts
    in
    	ModSyn.StrDec([name], nil, Dom, Insts)
    end
(* end RECON_MODULE *)
end
