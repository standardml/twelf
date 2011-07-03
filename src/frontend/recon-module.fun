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
  structure M = ModSyn

  type id = string list * Paths.region
  type openids = (id * (string * Paths.region)) list
  
  type sign = id list
  type morph = id list
  datatype syminst =
     coninst of id * (ExtSyn.term * Paths.region)
   | strinst of id * (morph       * Paths.region)
   | inclinst of morph * Paths.region
  type rel = id list
  datatype symcase =
     concase of id * (ExtSyn.term * Paths.region)
   | strcase of id * (rel       * Paths.region)
   | inclcase of rel * Paths.region

  datatype sigincl = sigincl of id * bool * openids
  
  datatype strdec = strdec of string * id * (syminst list) * openids * bool
                  | strdef of string * (morph * Paths.region) * bool

  datatype modbegin = sigbegin of string
                    | viewbegin of string * id * sign * bool
                    | relbegin of string * morph list * Paths.region
  
  datatype read = readfile of string
  datatype namespace = namespace of string option * URI.uri * Paths.region

(* end MODEXTSYN *)

(* implementing the remaining declarations of RECON_MODULE *)
  exception Error of string
  
  type ModExpElab = (ModSyn.Sign -> IDs.mid) * (ModSyn.Morph -> IDs.mid)
  
  (* local functions to handle errors *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))
        
  fun nameLookup expected (m : IDs.mid, names : IDs.Qid, r : Paths.region) =
     let val cOpt = (Names.nameLookup [expected] (m,names))
                    handle Names.Error(s) => error(r,s)
                         | Names.MissingModule(ns,modname, msg) => raise Names.MissingModule(ns,modname, Paths.wrap(r,msg))
     in
         case cOpt
           of SOME c => c
            | NONE => error(r, "undeclared identifier: " ^ IDs.foldQName names)
     end

  fun modNameLookup expected (m : IDs.mid, names : IDs.Qid, r : Paths.region) =
      let val m = M.cidToMid (nameLookup expected (m,names,r)) (* no exception possible in cidToMid if "expected" is a module level concept *)
      in
        if List.exists (fn (m',_) => m' = m) (M.getScope())
        then error(r, "module " ^ M.modFoldName m ^ " can only be used when closed")
        else m
      end

  fun init(hd:: nil) = nil
    | init(hd::tl) = hd :: (init tl)
  
  fun signToSign(nil) = M.Sign (M.currentMod())
    | signToSign((names,r)::nil) =
       let val s = modNameLookup Names.SIG (M.currentMod(), names, r)
       in M.Sign s
       end
    | signToSign((names,r)::tl) =
        let val s = modNameLookup Names.SIG (M.currentMod(), names, r)
        in M.SignUnion(M.Sign s, signToSign tl)
        end

  fun morphToMorph(cod : IDs.mid, (mor, r0)) =
     let
     	val (names, r) = List.last mor
     	val init = init mor
     	val (link, nextHome) = let val s = nameLookup Names.STRUC (cod, names, r)
     	                       in (M.MorStr s, M.strDecDom (M.structLookup s))
     	                       end
        handle _ => let val s = nameLookup Names.STRUC (M.currentMod(), names, r)
     	                   in (M.MorStr s, M.strDecDom (M.structLookup s))
     	                   end
        handle _ => let val m = modNameLookup Names.SIG (M.currentMod(), names, r)
                          in (M.MorId m, m)
                          end
        handle _ => let val m = modNameLookup Names.VIEW (M.currentMod(), names, r)
                         val M.ViewDec(_,_,dom,_,_,_) = M.modLookup m
                          in (M.MorView m, dom)
                          end
     in
     	if (init = nil)
     	then link
        else M.MorComp(morphToMorph(nextHome, (init, r0)), link)
     end

  (* composition of n-1 morphisms and one logical relation *)
  fun relToRel(_ : IDs.mid, (ids, r0)) = 
     let
     	val (rel,rrel) = List.last ids
     	val init = init ids
     	val m = modNameLookup Names.REL (M.currentMod(), rel, rrel)
     	val M.RelDec(_,_,dom,_,_) = M.modLookup m
     in
     	if init = nil
     	then M.Rel m
        else M.RelComp(morphToMorph(dom, (init, r0)), M.Rel m)
     end

  fun openToOpen(m,opens) = M.OpenDec (List.map
     (fn ((old,r),(new,_)) =>
       let val c = nameLookup Names.CON (m,old,r) handle Names.MissingModule _ => raise Error("unknown identifier")
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
             	val _ = case M.constDefOpt Con
                          of NONE => ()
                           | _ => error(r,
                              "instantiation of defined constant " ^ M.symFoldName Con ^ " not allowed");
             	(* if inferrable, expType holds the expected type to guide the term reconstruction *)
             	val _ = if M.inSignature() then
             	    case valOf (M.symVisible(Con, dom)) (* NONE impossible due to name lookup above *)
             	      of M.Self => ()
             	       | M.Included(_, NONE) => () (* instantiation of included but not meta-theory symbols is permitted in a structure *)
             	       | _ => error(r, "instantiation of inherited or meta-theory symbol " ^ M.symFoldName Con ^ " not allowed")
             	 else
             	    if (IDs.midOf Con = dom) then () else error(r, "instantiation of included or inherited constant " ^ M.symFoldName Con ^ " not allowed in a view");
             	val expType =
             	  if M.inSignature()
             	  then NONE                                                  (* instantiation in a structure *)
             	  else (
             	     SOME (Elab.applyMorph(M.constType Con,
             	                             M.MorView(M.currentMod())))     (* instantiation in a view *)
             	       handle Elab.MissingCase(m,c) =>
             	          error(rr, "instantiation for " ^ M.symFoldName Con ^
             	          " must occur after (possibly induced) instantiation for " ^ M.symFoldName c)
             	  )
               val job = case expType
                 of NONE => ExtSyn.jterm term
                  | SOME V => ExtSyn.jof'(term, V)
               val ExtSyn.JTerm((U, _), _, _) = ExtSyn.recon job
               val _ = ExtSyn.checkErrors(rr)
               val (impl, Term) = Abstract.abstractDecImp U
               val _ = if impl > 0 then error(r', "implicit arguments not allowed in instantiation") else ()
             (* val expImpl = M.constImp Con *)
             in
               M.ConInst(Con, NONE, Term)
		         (* error(rr, "mismatch in number of implicit arguments: instantiation " ^ Int.toString impl ^
		                                                     ", declaration " ^ Int.toString expImpl) *)
             end
         | strinst((names, r), (mor,r')) =>
             let
               (* @FR: check for visibility missing *)
             	val Str = nameLookup Names.STRUC (dom, names, r)
             	val Mor = morphToMorph (cod, (mor,r'))
             	val (_, _, Mor') = Elab.reconMorph Mor
             	             	   handle Elab.Error(msg) => error(r', msg)
             in
             	M.StrInst(Str, NONE, Mor')
             end
         | inclinst(mor, r) =>
             let
             	val Mor = morphToMorph (cod, (mor, r))
             	val (d, _, Mor') = Elab.reconMorph Mor
         	                   handle Elab.Error(msg) => error(r, msg)
             	val cid = case M.sigRel(d,dom)
             	          of SOME (M.Included(c,NONE)) => c
             	           | SOME (M.Included(c,SOME M.Meta)) => c
             	           | SOME (M.Included(c,SOME M.MetaIncluded)) =>
             	              error(r, "included morphism has domain " ^ M.modFoldName d ^
             	                       ", which is included into the meta-theory, but only a single morphism for the whole meta-theory is allowed")
             	           | SOME M.Self =>
             	              error(r, "included morphism has domain " ^ M.modFoldName d ^
             	                       ", which is the same as the domain of the link")
             	           | SOME _ =>
             	              error(r, "included morphism has domain " ^ M.modFoldName d ^
             	                       ", but instantiations for inclusions into the parent are not allowed")
             	           | NONE => error(r, "included morphism has domain " ^ M.modFoldName d ^
             	                          " which is not included into " ^ M.modFoldName dom)
             	(* @FR: we could permit M.Self here as well. Then structure/view definitions would be obsolete;
             	   the only problem is that the self-inclusion does not have a cid *)
             in
             	M.InclInst(cid, NONE, d, Mor')
             end
  
  fun symcaseToSymCase(dom : IDs.mid, cod : IDs.mid, cas : symcase, l) =
     case cas
        of concase((names, r), (term, r')) =>
             let
             	val rr = Paths.join(r,r')
             	val Con = nameLookup Names.CON (dom, names, r)
             	val _ = if (IDs.midOf Con = dom) then () else error(r,
             	   "case for included or inherited constant " ^ M.symFoldName Con ^ " not allowed")
             	val _ = case M.constDefOpt Con
                          of NONE => ()
                           | _ => error(r,
                              "case for defined constant " ^ M.symFoldName Con ^ " not allowed");
             	(* expected type to guide the term reconstruction *)
             	val expType = Elab.expType(Con, M.Rel(M.currentMod()))
             	              handle Elab.MissingCase(m,c) => error(rr, "case for " ^ M.symFoldName Con ^
             	                 " must occur after (possibly induced) case for " ^ M.symFoldName c)
		val ExtSyn.JTerm((U, _), _, _) = ExtSyn.recon (ExtSyn.jof'(term, expType))
                val _ = ExtSyn.checkErrors(rr)
		val (impl, Term) = Abstract.abstractDecImp U
		val _ = if impl > 0 then error(r', "implicit arguments not allowed in logical relation") else ()
		(* val expImpl = M.constImp Con *)
		(* error(rr, "mismatch in number of implicit arguments: instantiation " ^ Int.toString impl ^
		                                                     ", declaration " ^ Int.toString expImpl) *)
             in
		M.ConCase(Con, NONE, Term)
             end
         | strcase((names, r), (rel, r')) =>
             let
             	val Str = nameLookup Names.STRUC(dom, names, r)
             	val Rel = relToRel (cod, (rel,r'))
             	val (_, _, _, Rel') = Elab.reconRel Rel
             	                      handle Elab.Error(msg) => error(r', msg)
             in
             	M.StrCase(Str, NONE, Rel')
             end
         | inclcase(rel, r) =>
             let
             	val Rel = relToRel(cod, (rel, r))
             	val (d, _, _, Rel') = Elab.reconRel Rel
             	                      handle Elab.Error(msg) => error(r, msg)
             	val cid = case List.find
             	               (fn M.ObjSig(m,M.Included _) => m = d | _ => false)
             	               (M.modInclLookup dom)
             	          of SOME (M.ObjSig(_, M.Included(c,NONE))) => c
             	           | SOME (M.ObjSig(_, M.Included(c,SOME M.Meta))) => c
             	           | SOME (M.ObjSig(_, M.Included(c,SOME M.MetaIncluded))) =>
             	              error(r, "included logical relation has domain " ^ M.modFoldName d ^
             	                       ", which is included into the meta-theory, but only a single logical relation for the whole meta-theory is allowed")
             	           | NONE => error(r, "included logical relation has domain " ^ M.modFoldName d ^
             	                          " which is not included into " ^ M.modFoldName dom)
             in
             	M.InclCase(cid, NONE, Rel')
             end

   fun siginclToSigIncl(sigincl ((name,r), isMeta, opens), _) =
      let
      	 val m = modNameLookup Names.SIG (M.currentMod(), name, r)
	 val Opens = openToOpen (m,opens)
      in
      	 M.SigIncl (m, isMeta, Opens, false)
      end

   fun strdecToStrDec(strdec(name : string, (dom : string list, r1 : Paths.region),
                            insts : syminst list, opens : openids, implicit : bool), loc) = 
    let
    	val Cod = M.currentTargetSig()
    	val Dom : IDs.mid = modNameLookup Names.SIG (Cod, dom, r1)
    	val Insts = List.map (fn x => syminstToSymInst(Dom, Cod, x,loc)) insts
	val Opens = openToOpen (Dom,opens)
    in
    	M.StrDec([name], nil, Dom, Insts, Opens, implicit)
    end
    | strdecToStrDec(strdef(name : string, morr, implicit : bool), l) =
       let
       	  val Mor = morphToMorph(M.currentTargetSig(), morr)
       	  val (Dom, _, Mor') = Elab.reconMorph Mor (* @FR: taking domain of first link is enough here *)
       in
       	  M.StrDef([name], nil, Dom, Mor', implicit)
       end
   
   exception ElaborateSignUnion of M.Sign * (IDs.mid -> ModSyn.ModDec)
   fun modbeginToModDec(sigbegin name, Paths.Loc(fileName, _), (signExpElab, morExpElab)) =
       let val parname = M.modDecName (M.modLookup (M.currentMod()))
       in  M.SigDec(Names.getCurrentNS(NONE), parname @ [name], NONE)
       end
     | modbeginToModDec(viewbegin(name, (dom,rd), cod, implicit), Paths.Loc(fileName, _), (signExpElab, morExpElab)) =
         let
            val cur = M.currentMod()
            val parname = M.modDecName (M.modLookup cur)
            val Dom = modNameLookup Names.SIG (cur, dom, rd)
            val (CodId, Origin) = case signToSign cod
               of M.Sign m => (m, NONE)
                | sign => (signExpElab sign, SOME sign) 
         in
            M.ViewDec (Names.getCurrentNS(NONE), parname @ [name], Dom, CodId, Origin, implicit)
         end
     | modbeginToModDec(relbegin(name, mors, r), loc as Paths.Loc(fileName, _), (signExpElab, morExpElab)) =
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
            val parname = M.modDecName (M.modLookup (M.currentMod()))
         in
            M.RelDec (Names.getCurrentNS(NONE), parname @ [name], dom, cod, Mors')
         end

   fun readToRead(readfile name, Paths.Loc(fileName, r)) =
     if M.onToplevel()
     then M.ReadFile (String.substring(name, 1, (String.size name) - 2)) (* remove "" *)
     else error(r, "%read only legal on toplevel")
end (* end RECON_MODULE *)
