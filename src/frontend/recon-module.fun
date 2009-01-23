(* Reconstruction for modular expressions *)
(* Author: Florian Rabe *)

functor ReconModule
  (structure Global : GLOBAL
   structure Names : NAMES
   structure ReconTerm' : RECON_TERM
   structure ModSyn' : MODSYN
  )
  : RECON_MODULE =
struct

(* implementing the signature MODEXTSYN *)
  structure ExtSyn = ReconTerm'

  type morph = (string list * Paths.region) list
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
  fun morphToMorph(cod : IDs.mid, (mor, r0)) =
     let
     	val (names, r) = List.last mor
     	val init = List.take (mor, (List.length mor) - 1)
     	val (link, nextCod) = let val s = nameLookupWithError STRUC (cod, names, r)
     	                      in (ModSyn.MorStr s, ModSyn.strDecDom (ModSyn.structLookup s))
     	                      end
            handle Error _ => let val m = modnameLookupWithError VIEW (names, r)
                                  val ModSyn.ViewDec(_,dom,_) = ModSyn.modLookup m
                              in (ModSyn.MorView m, dom)
                              end
     in
     	if (init = nil)
     	then link
        else ModSyn.MorComp(morphToMorph(nextCod, (init, r0)), link)
     end

  fun syminstToSymInst(dom : IDs.mid, cod : IDs.mid, inst : syminst, l as Paths.Loc (fileName, r)) =
     case inst
        of coninst((names, r), (term, r')) =>
             let
             	val Con = nameLookupWithError CON (dom, names, r)
             	(* if inferrable, expType holds the expected type to guide the term reconstruction *)
             	val expType =
             	  if ModSyn.inSignature()
             	  then NONE                                                            (* instantiation in a structure *)
             	  else SOME (Elab.applyMorph(ModSyn.constType Con,
             	                             ModSyn.MorView(ModSyn.currentMod())))     (* instantiation in a view *)
             	       handle Elab.UndefinedMorph(_,c) =>
             	          error(Paths.join(r,r'), "instantiation for " ^ ModSyn.symFoldName Con ^
             	          " must occur after instantiation for " ^ ModSyn.symFoldName c)
             	val job = case expType
             	  of NONE => ExtSyn.jterm term
             	   | SOME V => ExtSyn.jof'(term, V)
		val Term = (case ExtSyn.recon job
		   of ExtSyn.JTerm((U, _), _, _) => U
		    | ExtSyn.JOf((U,_), _, _) => U
		   ) handle _ => raise Error ""
             in
             	ModSyn.ConInst(Con, Term)
             end
        
         | strinst((names, r), mor) =>
             let
             	val Str = nameLookupWithError STRUC (dom, names, r)
             	val Mor = morphToMorph (cod, mor)
             in
             	ModSyn.StrInst(Str, Mor)
             end
  
  fun strdecToStrDec(strdec(name : string, (dom : string list, r1 : Paths.region), insts : syminst list),
                     l as Paths.Loc (fileName, r2)
  ) = 
    let
    	val Dom : IDs.mid = modnameLookupWithError SIG (dom, r1)
    	val Cod = ModSyn.currentTargetSig()
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
