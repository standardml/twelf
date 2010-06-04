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

  type id = string list * Paths.region
  type openids = (id * (string * Paths.region)) list
  
  type morph = id list
  datatype syminst =
     coninst of id * (ExtSyn.term * Paths.region)
   | strinst of id * (morph       * Paths.region)
   | inclinst of morph * Paths.region

  datatype sigincl = sigincl of id * openids
  
  datatype strdec = strdec of string * id * (syminst list) * openids * bool
                  | strdef of string * (morph * Paths.region) * bool

  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * id * bool
  
  datatype read = readfile of string
  
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

  fun modnameLookupWithError expected (l : IDs.Qid, r : Paths.region) =
     case Names.modnameLookup l
       of SOME m => (
           case (expected, ModSyn.modLookup m)
             of (SIG, ModSyn.SigDec _ ) => m
              | (VIEW, ModSyn.ViewDec _) => m
              | _ => error(r, "concept mismatch, expected " ^ expToString expected ^ ": " ^ Names.foldQualifiedName l)
          )
        | NONE => error(r, "undeclared identifier: " ^ Names.foldQualifiedName l)

  fun morphToMorph(cod : IDs.mid, (mor, r0)) =
     let
     	val (names, r) = List.last mor
     	val init = List.take (mor, (List.length mor) - 1)
     	val (link, nextCod) = let val s = nameLookupWithError STRUC (cod, names, r)
     	                      in (ModSyn.MorStr s, ModSyn.strDecDom (ModSyn.structLookup s))
     	                      end
            handle Error _ => let val m = modnameLookupWithError VIEW (names, r)
                                  val ModSyn.ViewDec(_,_,dom,_,_) = ModSyn.modLookup m
                              in (ModSyn.MorView m, dom)
                              end
     in
     	if (init = nil)
     	then link
        else ModSyn.MorComp(morphToMorph(nextCod, (init, r0)), link)
     end

  fun openToOpen(m,opens) = ModSyn.OpenDec (List.map
     (fn ((old,r),(new,_)) =>
       let val c = nameLookupWithError CON (m,old,r)
       in (c, new)
       end
     )
     opens)

  fun syminstToSymInst(dom : IDs.mid, cod : IDs.mid, inst : syminst, l) =
     case inst
        of coninst((names, r), (term, r')) =>
             let
             	val rr = Paths.join(r,r')
             	val Con = nameLookupWithError CON (dom, names, r)
             	val _ = if (IDs.midOf Con = dom) then () else error(r,
             	   "instantiation of included constant " ^ ModSyn.symFoldName Con ^ " not allowed")
             	val _ = case ModSyn.constDefOpt Con
                          of NONE => ()
                           | _ => raise Error(
                              "instantiation of defined constant " ^ ModSyn.symFoldName Con ^ " not allowed");
             	(* if inferrable, expType holds the expected type to guide the term reconstruction *)
             	val expType =
             	  if ModSyn.inSignature()
             	  then NONE                                                            (* instantiation in a structure *)
             	  else SOME (Elab.applyMorph(ModSyn.constType Con,
             	                             ModSyn.MorView(ModSyn.currentMod())))     (* instantiation in a view *)
             	       handle Elab.UndefinedMorph(_,c) =>
             	          error(rr, "instantiation for " ^ ModSyn.symFoldName Con ^
             	          " must occur after (possibly induced) instantiation for " ^ ModSyn.symFoldName c)
             	val job = case expType
             	  of NONE => ExtSyn.jterm term
             	   | SOME V => ExtSyn.jof'(term, V)
		val ExtSyn.JTerm((U, _), _, _) = ExtSyn.recon job
                val _ = ExtSyn.checkErrors(rr)
		val (impl, Term) = Abstract.abstractDecImp U
		val _ = if impl > 0 then error(r', "implicit arguments not allowed in instantiation") else ()
		(* val expImpl = ModSyn.constImp Con *)
             in
		ModSyn.ConInst(Con, NONE, Term)
		(* error(rr, "mismatch in number of implicit arguments: instantiation " ^ Int.toString impl ^
		                                                                         ", declaration " ^ Int.toString expImpl) *)
             end
         | strinst((names, r), mor) =>
             let
             	val Str = nameLookupWithError STRUC (dom, names, r)
             	val Mor = morphToMorph (cod, mor)
             in
             	ModSyn.StrInst(Str, NONE, Mor)
             end
         | inclinst(mor, r) =>
             let
             	val Mor = morphToMorph (cod, (mor, r))
             	val (d, _, Mor') = Elab.reconMorph Mor
             	val cid = case List.find
             	               (fn (m,ModSyn.Included (SOME _)) => m = d | _ => false)
             	               (ModSyn.sigRelLookup dom)
             	          of SOME (_, ModSyn.Included (SOME c)) => c
             	           | NONE => raise Error("included morphism has domain " ^ ModSyn.modFoldName d ^
             	                          " which is not included directly into " ^ ModSyn.modFoldName dom)
             in
             	ModSyn.InclInst(cid, NONE, Mor')
             end
  
   fun siginclToSigIncl(sigincl (sigid, opens), _) =
      let
      	 val m = modnameLookupWithError SIG sigid
	 val Opens = openToOpen (m,opens)
      in
      	 ModSyn.SigIncl (m, Opens)
      end

  fun strdecToStrDec(strdec(name : string, (dom : string list, r1 : Paths.region),
                            insts : syminst list, opens : openids, implicit : bool), loc) = 
    let
    	val Dom : IDs.mid = modnameLookupWithError SIG (dom, r1)
    	val Cod = ModSyn.currentTargetSig()
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,loc)) insts
	val Opens = openToOpen (Dom,opens)
    in
    	ModSyn.StrDec([name], nil, Dom, Insts, Opens, implicit)
    end
    | strdecToStrDec(strdef(name : string, morr, implicit : bool), l) =
       let
       	  val Mor = morphToMorph(ModSyn.currentTargetSig(), morr)
       	  val (Dom, _, _) = Elab.reconMorph Mor (* @FR: taking domain of first link is enough here *)
       in
       	  ModSyn.StrDef([name], nil, Dom, Mor, implicit)
       end
    
   fun modbeginToModDec(sigbegin name, Paths.Loc(fileName, _)) = ModSyn.SigDec(OS.Path.mkCanonical fileName, [name])
     | modbeginToModDec(viewbegin(name, dom, cod, implicit), Paths.Loc(fileName, _)) =
         let
            val Dom = modnameLookupWithError SIG dom
            val Cod = modnameLookupWithError SIG cod
         in
            ModSyn.ViewDec (OS.Path.mkCanonical fileName, [name], Dom, Cod, implicit)
         end

   fun readToRead(readfile name, Paths.Loc(fileName, r)) =
     if ModSyn.onToplevel()
     then ModSyn.ReadFile (String.substring(name, 1, (String.size name) - 2)) (* remove "" *)
     else error(r, "%read only legal on toplevel")
end (* end RECON_MODULE *)
