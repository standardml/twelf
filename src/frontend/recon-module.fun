(* Reconstruction for modular expressions *)
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

  datatype morph = morlink of (string list * Paths.region)
  datatype syminst =
     coninst of (string list * Paths.region) * (ExtSyn.term * Paths.region)
   | strinst of (string list * Paths.region) * (morph       * Paths.region)

  datatype strdec = strdec of string * (string list * Paths.region) * (syminst list)
                  | strdef of string * (morph * Paths.region)

  datatype modbegin = sigbegin of string
                    | viewbegin of string * (string list * Paths.region) * (string list * Paths.region)
  
  type siginclude = unit
  type stropen = unit
(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string

  (* local functions to handle errors *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))
  
  datatype Expected = SIG | VIEW | CON | STRUC
  fun expToString SIG = "signature"
    | expToString VIEW = "view"
    | expToString CON = "constant"
    | expToString STRUC = "structure"
        
  fun nameLookupWithError expected (m : IDs.mid, l : IDs.Qid, r : Paths.region) =
     case Names.nameLookup (m,l)
       of SOME c => (
           case (expected, ModSyn.symLookup c)
             of (CON, ModSyn.SymCon _ ) => c
              | (STRUC, ModSyn.SymStr _) => c
              | _ => error(r, "concept mismatch, expected " ^ expToString expected ^ ": " ^ Names.foldQualifiedName l)
          )
        | NONE => error(r, "undeclared identifier: " ^ Names.foldQualifiedName l)

  fun modnameLookupWithError expected (l : string list, r : Paths.region) =
     case Names.modnameLookup l
       of SOME m => (
           case (expected, ModSyn.modLookup m)
             of (SIG, ModSyn.SigDec _ ) => m
              | (VIEW, ModSyn.ViewDec _) => m
              | _ => error(r, "concept mismatch, expected " ^ expToString expected ^ ": " ^ Names.foldQualifiedName l)
          )
        | NONE => error(r, "undeclared identifier: " ^ Names.foldQualifiedName l)

(* @CS: is all the paths stuff right in the sequel *)
  fun morphToMorph(Dom : IDs.mid, Cod : IDs.mid, (mor, r)) =
     case mor
       of morlink(names, r) => ModSyn.MorStr (nameLookupWithError STRUC (Cod, names, r))
             handle Error _ => ModSyn.MorView (modnameLookupWithError VIEW (names, r))
  
  fun syminstToSymInst(Dom : IDs.mid, Cod : IDs.mid, inst : syminst, l as Paths.Loc (fileName, r)) =
     case inst
        of coninst((names, r), (term, _)) =>
             let
             	val Con = nameLookupWithError CON (Dom, names, r)
		val ExtSyn.JTerm((Term, occ), V, L) = ExtSyn.recon (ExtSyn.jterm term)
             in
             	ModSyn.ConInst(Con, Term)
             end
        
         | strinst((names, r), mor) =>
             let
             	val Str = nameLookupWithError STRUC (Dom, names, r)
             	val Mor = morphToMorph (Dom, Cod, mor)
             in
             	ModSyn.StrInst(Str, Mor)
             end
  
  fun strdecToStrDec(Cod : IDs.mid, strdec(name : string, (dom : string list, r1 : Paths.region), insts : syminst list),
                     l as Paths.Loc (fileName, r2)
  ) = 
    let
    	val Dom : IDs.mid = modnameLookupWithError SIG (dom, r1)
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,l)) insts
    in
    	ModSyn.StrDec([name], nil, Dom, Insts)
    end
    
   fun modbeginToModDec(sigbegin name) = ModSyn.SigDec [name]
     | modbeginToModDec(viewbegin(name, dom, cod)) =
         let
            val Dom = modnameLookupWithError SIG dom
            val Cod = modnameLookupWithError SIG cod
         in
            ModSyn.ViewDec ([name], Dom, Cod)
         end
end (* end RECON_MODULE *)
