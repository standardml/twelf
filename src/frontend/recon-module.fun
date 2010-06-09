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
  type rel = id
  datatype symcase =
     concase of id * (ExtSyn.term * Paths.region)
   | strcase of id * (rel       * Paths.region)
   | inclcase of rel * Paths.region

  datatype sigincl = sigincl of id * openids
  
  datatype strdec = strdec of string * id * (syminst list) * openids * bool
                  | strdef of string * (morph * Paths.region) * bool

  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * id * bool
                    | relbegin of string * morph list * Paths.region
  
  datatype read = readfile of string

(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string

  (* local functions to handle errors *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))
        
  fun nameLookup expected (m : IDs.mid, names : IDs.Qid, r : Paths.region) =
     let val cOpt = (Names.nameLookup [expected] (m,names))
                    handle Names.Error(s) => error(r,s)
     in
         case cOpt
           of SOME c => c
            | NONE => error(r, "undeclared identifier: " ^ IDs.foldQName names)
      end

  fun modNameLookup' expected (m : IDs.mid, names : IDs.Qid, r : Paths.region) =
      ModSyn.cidToMid (nameLookup expected (m,names,r))
      (* no exception possible in cidToMid if "expected" is a module level concept *)

  (* as modNameLookup' but also checks that the module is closed
     this is call for all modules except for the codomain of views and relations, which may be open *)
  fun modNameLookup expected (m : IDs.mid, names : IDs.Qid, r : Paths.region) =
      let val m = modNameLookup' expected (m,names,r)
      in
        if List.exists (fn (m',_) => m' = m) (ModSyn.getScope())
        then error(r, "module " ^ ModSyn.modFoldName m ^ " can only be used when closed")
        else m
      end

  fun morphToMorph(home : IDs.mid, (mor, r0)) =
     let
     	val (names, r) = List.last mor
     	val init = List.take (mor, (List.length mor) - 1)
     	val (link, nextHome) = let val s = nameLookup Names.STRUC (home, names, r)
     	                       in (ModSyn.MorStr s, ModSyn.strDecDom (ModSyn.structLookup s))
     	                       end
            handle Error _ => let val m = modNameLookup Names.VIEW (ModSyn.currentMod(), names, r)
                                  val ModSyn.ViewDec(_,_,dom,_,_) = ModSyn.modLookup m
                              in (ModSyn.MorView m, dom)
                              end
     in
     	if (init = nil)
     	then link
        else ModSyn.MorComp(morphToMorph(nextHome, (init, r0)), link)
     end

  fun relToRel(home : IDs.mid, ((names, r), r0)) = 
     let
     	val m = modNameLookup Names.REL (home, names, r)
     in
     	ModSyn.Rel m
     end
  
  fun openToOpen(m,opens) = ModSyn.OpenDec (List.map
     (fn ((old,r),(new,_)) =>
       let val c = nameLookup Names.CON (m,old,r)
       in (c, new)
       end
     )
     opens)

  fun syminstToSymInst(dom : IDs.mid, cod : IDs.mid, inst : syminst, l) =
     case inst
        of coninst((names, r), (term, r')) =>
             let
             	val rr = Paths.join(r,r')
             	val Con = nameLookup Names.CON (dom, names, r)
             	val _ = if (IDs.midOf Con = dom) then () else error(r,
             	   "instantiation of included or inherited constant " ^ ModSyn.symFoldName Con ^ " not allowed")
             	val _ = case ModSyn.constDefOpt Con
                          of NONE => ()
                           | _ => error(r,
                              "instantiation of defined constant " ^ ModSyn.symFoldName Con ^ " not allowed");
             	(* if inferrable, expType holds the expected type to guide the term reconstruction *)
             	val expType =
             	  if ModSyn.inSignature()
             	  then NONE                                                            (* instantiation in a structure *)
             	  else SOME (Elab.applyMorph(ModSyn.constType Con,
             	                             ModSyn.MorView(ModSyn.currentMod())))     (* instantiation in a view *)
             	       handle Elab.MissingCase(m,c) =>
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
             	val Str = nameLookup Names.STRUC (dom, names, r)
             	val Mor = morphToMorph (cod, mor)
             	val (_, _, Mor') = Elab.reconMorph Mor
             in
             	ModSyn.StrInst(Str, NONE, Mor')
             end
         | inclinst(mor, r) =>
             let
             	val Mor = morphToMorph (cod, (mor, r))
             	val (d, _, Mor') = Elab.reconMorph Mor
             	val incl = List.find (fn ModSyn.ObjSig(m,ModSyn.Included (SOME _)) => m = d | _ => false)
             	                     (ModSyn.modInclLookup dom)
             	val cid = case incl
             	          of SOME (ModSyn.ObjSig(_, ModSyn.Included (SOME c))) => c
             	           | NONE => error(r, "included morphism has domain " ^ ModSyn.modFoldName d ^
             	                          " which is not included directly into " ^ ModSyn.modFoldName dom)
             in
             	ModSyn.InclInst(cid, NONE, Mor')
             end
  
  fun symcaseToSymCase(dom : IDs.mid, cod : IDs.mid, cas : symcase, l) =
     case cas
        of concase((names, r), (term, r')) =>
             let
             	val rr = Paths.join(r,r')
             	val Con = nameLookup Names.CON (dom, names, r)
             	val _ = if (IDs.midOf Con = dom) then () else error(r,
             	   "case for included or inherited constant " ^ ModSyn.symFoldName Con ^ " not allowed")
             	val _ = case ModSyn.constDefOpt Con
                          of NONE => ()
                           | _ => error(r,
                              "case for defined constant " ^ ModSyn.symFoldName Con ^ " not allowed");
             	(* expected type to guide the term reconstruction *)
             	val expType = Elab.applyRel(ModSyn.constType Con, ModSyn.Rel(ModSyn.currentMod()))
             	       handle Elab.MissingCase(m,c) =>
             	          error(rr, "case for " ^ ModSyn.symFoldName Con ^
             	          " must occur after (possibly induced) case for " ^ ModSyn.symFoldName c)
		val ExtSyn.JTerm((U, _), _, _) = ExtSyn.recon (ExtSyn.jof'(term, expType))
                val _ = ExtSyn.checkErrors(rr)
		val (impl, Term) = Abstract.abstractDecImp U
		val _ = if impl > 0 then error(r', "implicit arguments not allowed in logical relation") else ()
		(* val expImpl = ModSyn.constImp Con *)
		(* error(rr, "mismatch in number of implicit arguments: instantiation " ^ Int.toString impl ^
		                                                                         ", declaration " ^ Int.toString expImpl) *)
             in
		ModSyn.ConCase(Con, NONE, Term)
             end
         | strcase((names, r), rel) =>
             let
             	val Str = nameLookup Names.STRUC(dom, names, r)
             	val Rel = relToRel (cod, rel)
             	val (_, _, _, Rel') = Elab.reconRel Rel
             in
             	ModSyn.StrCase(Str, NONE, Rel')
             end
         | inclcase(rel, r) =>
             let
             	val Rel = relToRel(cod, (rel, r))
             	val (d, _, _, Rel') = Elab.reconRel Rel
             	val cid = case List.find
             	               (fn ModSyn.ObjSig(m,ModSyn.Included (SOME _)) => m = d | _ => false)
             	               (ModSyn.modInclLookup dom)
             	          of SOME (ModSyn.ObjSig(_, ModSyn.Included (SOME c))) => c
             	           | NONE => raise error(r, "included logical relation has domain " ^ ModSyn.modFoldName d ^
             	                          " which is not included directly into " ^ ModSyn.modFoldName dom)
             in
             	ModSyn.InclCase(cid, NONE, Rel')
             end

   fun siginclToSigIncl(sigincl ((name,r), opens), _) =
      let
      	 val m = modNameLookup Names.SIG (ModSyn.currentMod(), name, r)
	 val Opens = openToOpen (m,opens)
      in
      	 ModSyn.SigIncl (m, Opens)
      end

   fun strdecToStrDec(strdec(name : string, (dom : string list, r1 : Paths.region),
                            insts : syminst list, opens : openids, implicit : bool), loc) = 
    let
    	val Cod = ModSyn.currentTargetSig()
    	val Dom : IDs.mid = modNameLookup Names.SIG (Cod, dom, r1)
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,loc)) insts
	val Opens = openToOpen (Dom,opens)
    in
    	ModSyn.StrDec([name], nil, Dom, Insts, Opens, implicit)
    end
    | strdecToStrDec(strdef(name : string, morr, implicit : bool), l) =
       let
       	  val Mor = morphToMorph(ModSyn.currentTargetSig(), morr)
       	  val (Dom, _, Mor') = Elab.reconMorph Mor (* @FR: taking domain of first link is enough here *)
       in
       	  ModSyn.StrDef([name], nil, Dom, Mor', implicit)
       end
    
   fun modbeginToModDec(sigbegin name, Paths.Loc(fileName, _)) =
       let val parname = ModSyn.modDecName (ModSyn.modLookup (ModSyn.currentMod()))
       in  ModSyn.SigDec(OS.Path.mkCanonical fileName, parname @ [name])
       end
     | modbeginToModDec(viewbegin(name, (dom,rd), (cod,rc), implicit), Paths.Loc(fileName, _)) =
         let
            val cur = ModSyn.currentMod()
            val Dom = modNameLookup Names.SIG (cur, dom, rd)
            val Cod = modNameLookup' Names.SIG (cur, cod, rc)
            val parname = ModSyn.modDecName (ModSyn.modLookup (ModSyn.currentMod()))
         in
            ModSyn.ViewDec (OS.Path.mkCanonical fileName, parname @ [name], Dom, Cod, implicit)
         end
     | modbeginToModDec(relbegin(name, mors, r), loc as Paths.Loc(fileName, _)) =
         let
            val _ = if mors = nil then error(r, "logical relation must have at least one morphism") else ()
            val Mors = List.map (fn x => morphToMorph(0, (x, loc))) mors
            val (dom :: doms, cod :: cods, Mors') =
                let val recmors = List.map Elab.reconMorph Mors
                in (List.map #1 recmors, List.map #2 recmors, List.map #3 recmors)
                end
            val _ = if List.exists (fn x => not(x = dom)) doms
                    then error(r, "morphisms do not have the same domain")
                    else ()
            val _ = if List.exists (fn x => not(x = cod)) cods
                    then raise error(r, "morphisms do not have the same codomain")
                    else ()
            val parname = ModSyn.modDecName (ModSyn.modLookup (ModSyn.currentMod()))
         in
            ModSyn.RelDec (OS.Path.mkCanonical fileName, parname @ [name], dom, cod, Mors')
         end

   fun readToRead(readfile name, Paths.Loc(fileName, r)) =
     if ModSyn.onToplevel()
     then ModSyn.ReadFile (String.substring(name, 1, (String.size name) - 2)) (* remove "" *)
     else error(r, "%read only legal on toplevel")
end (* end RECON_MODULE *)
