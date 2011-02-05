(* Printing to OMDoc *)
(* Author: Florian Rabe, based on print.fun *)

functor PrintOMDoc(
   structure Whnf : WHNF
   structure Names : NAMES
   structure Origins : ORIGINS
   structure Comments : COMMENTS
)
  : PRINTFILE =
struct

  structure I = IntSyn

  (* Indentation
     indent : current indentation width
     nl_ind()() : newline and indent
     nl_unind()() : newline and unindent
     nl() : newline (keeping current indentation)
  *)
  val indent = ref 0
  val tabstring = "   "
  fun tabs(n) = if (n <= 0) then "" else tabstring ^ tabs(n-1)
  fun ind_reset() = (indent := 0)
  fun ind(n) = indent := !indent + n
  fun unind(n) = indent := !indent - n
  fun nl_ind() = (indent := !indent + 1; "\n" ^ tabs(!indent))
  fun nl_unind() = (indent := !indent - 1; "\n" ^ tabs(!indent))
  fun nl() = "\n" ^ tabs(!indent)
  
  (* XML and OMDoc escaping
     Among the printable non-whitespace ascii characters, the following are not URI pchars (RFC 3986): "#%&/<>?[\]^`{|}
     We have to escape "&<> for XML and ?/% for OMDoc. The others must only be encoded in URI references.
     These are actually possible in Twelf names: "#&/<>?\^`| *)
  fun escape s = let 
	  fun escapelist nil = nil
	    | escapelist (#"&" :: rest) = String.explode "&amp;" @ (escapelist rest)
	    | escapelist (#"<" :: rest) = String.explode "&lt;" @ (escapelist rest) 
	    | escapelist (#">" :: rest) = String.explode "&gt;" @ (escapelist rest)
	    | escapelist (#"\"" :: rest) = String.explode "&quot;" @ (escapelist rest)
	    | escapelist (#"?" :: rest) = String.explode "%3F" @ (escapelist rest)
	    | escapelist (#"/" :: rest) = String.explode "%2F" @ (escapelist rest)
	    | escapelist (c :: rest) = c :: (escapelist rest)
  in
    String.implode (escapelist (String.explode s))
  end
  
  (* locations of meta theories *)
  val baseMMT = "http://cds.omdoc.org/omdoc/mmt.omdoc"
  val baseLF = "http://cds.omdoc.org/foundations/lf/lf.omdoc"
  val cdMMT = ["mmt"]
  val cdLF = ["lf"]
  val cdTwelf = "twelf"
  
  (* XML and OMDoc constructors, return string *)
  fun ElemOpen'(label, attrs) = "<" ^ label ^ (if attrs = nil then "" else " " ) ^ IDs.mkString(attrs, "", " ", "")
  fun ElemOpen(label, attrs) = ElemOpen'(label, attrs) ^ ">"
  fun ElemClose(label) = "</" ^ label ^ ">"
  fun ElemEmpty(label, attrs) = ElemOpen'(label, attrs) ^ "/>"
  fun Attr(label, value) = label ^ "=\"" ^ value ^ "\""
  fun localPath(comps) = IDs.mkString(List.map escape comps, "", "/", "")
  fun mpath(doc, module) = doc ^ "?" ^ (localPath module)
  fun OMS3(base, module, name) = let
     val baseA = if base = "" then nil else [Attr("base", base)]
     val modA = if module = nil then nil else [Attr("module", localPath module)]
     val nameA = if name = nil then nil else [Attr("name", localPath name)]
   in
      ElemEmpty("om:OMS", baseA @ modA @ nameA)
   end
  fun LFOMS(name) = OMS3(baseLF, cdLF,name)
  fun MMTOMS(name) = OMS3(baseMMT, cdMMT,name)
  fun OMV(name) = ElemEmpty("om:OMV", [Attr("name", escape name)])
  fun OMA(func, args) = "<om:OMA>" ^ nl_ind() ^ func ^ nl() ^ IDs.mkString(args, "", nl(), "") ^ nl_unind() ^ "</om:OMA>"
  fun OMBIND(bind, vars, scope) = "<om:OMBIND>" ^ nl_ind() ^ bind ^ nl() ^ vars ^ nl() ^ scope ^ nl_unind() ^ "</om:OMBIND>"
  fun OM1ATTR(obj, key, value) = "<om:OMATTR><om:OMATP>" ^ nl_ind() ^ key ^ nl() ^ value ^ nl() ^ "</om:OMATP>" ^
                                 obj ^ nl_unind() ^ "</om:OMATTR>"
  fun OM1BVAR(var, key, value) = "<om:OMBVAR>" ^ nl_ind() ^ OM1ATTR(var, key, value) ^ nl_unind() ^ "</om:OMBVAR>"
  
  type Path = {isAbs : bool, vol : string, arcs : string list}
  
  (* arguments of the recursion: baseNS, current identify the module relative to which addresses are given
     for theories the theory, for views (except for @from and @to) the codomain
   *)
  type Params = {baseNS : URI.uri, current : IDs.mid}
  
  (* Printing references *)
  
  fun omdocExtension s = (if String.isSuffix ".elf" s then substring(s, 0, String.size s - 4) else s) ^ ".omdoc"
  fun diff(nil, nil) = nil
    | diff(hd::tl, hdf::tlf) =
      if hd = hdf
      then diff(tl, tlf)
      else (List.map (fn _ => "..") tl) @ (hdf :: tlf)
  fun pathToArcList(p: Path) = if #isAbs p andalso not(#vol p = "") then #vol p :: #arcs p else #arcs p
  (* compute document reference (URI) relative to params *)
  fun relDocName(f, baseNS) = 
    let
       val file = OS.Path.fromString (URI.uriToString f)
       val dif = case List.rev (diff(pathToArcList (OS.Path.fromString (URI.uriToString baseNS)), pathToArcList file))
         of nil => nil
          | hd :: tl => List.rev ((omdocExtension hd) :: tl)
    in
       IDs.mkString(dif, "", "/", "")
    end
  (* compute module reference (URI) relative to params *)
  fun relModName(m, params : Params) =
    let val dec = ModSyn.modLookup m
    in mpath(relDocName (ModSyn.modDecBase dec, #baseNS params), ModSyn.modDecName dec)
    end
  (* compute module reference (OMS) relative to params *)
  fun relModOMS (m, params : Params) =
    let val dec = ModSyn.modLookup m
        val doc = relDocName (ModSyn.modDecBase dec, #baseNS params)
        val md = ModSyn.modDecName dec
    in OMS3(doc, md, nil)
    end
  (* compute symbol reference (URI) relative to params *)
  fun relSymName (c, params : Params) =
    let val dec = ModSyn.modLookup (IDs.midOf c)
    in mpath(relDocName (ModSyn.modDecBase dec, #baseNS params), ModSyn.modDecName dec) ^ 
             "?" ^ (localPath (ModSyn.symName c))
    end
  (* compute symbol reference (OMS) relative to params *)
  fun relSymOMS (c, params : Params) =
    let
        val m = IDs.midOf c
        val dec = ModSyn.modLookup m
        val doc = if m = 0 orelse m = #current params then "" else relDocName (ModSyn.modDecBase dec, #baseNS params)
        val md = if m = #current params then nil else ModSyn.modDecName dec
    in OMS3(doc, md, ModSyn.symName c)
    end

  (* Printing expressions *)
  
  (* check how many arguments there will be in an om:OMA element *)
  fun spineLength I.Nil = 0
    | spineLength (I.SClo (S, _)) = spineLength S
    | spineLength (I.App(_, S)) = 1 + (spineLength S)

  fun fmtCon (G, I.BVar(x), params) = 
      let
	val I.Dec (I.VarInfo(SOME n,_,_,_), _) = I.ctxDec (G, x)
      in 
	OMV(n)
      end
    | fmtCon (G, I.Const(cid), params) = relSymOMS (cid, params)
    | fmtCon (G, I.Def(cid), params) = relSymOMS (cid, params)
    | fmtCon (G, I.NSDef(cid), params) = relSymOMS (cid, params)
    | fmtCon (G, I.FgnConst (csid, condec), _) = "FgnConst"  (* FIX -cs Fri Jan 28 17:45:35 2005*)
    (* I.Skonst, I.FVar cases should be impossible *)

  fun fmtUni (I.Type) = LFOMS(["type"])
    | fmtUni (I.Kind) = LFOMS(["kind"])

  (* fmtExpW (G, (U, s)) = fmt
     format the expression U[s].
     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)

  (* argument imp could be removed; testing for implicit variables can be done using the VarInfo *)
  fun fmtExpW (G, (I.Uni(L), s), _, _) = fmtUni L
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s), imp, params) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val (D' as I.Dec (I.VarInfo(SOME(name),r,e,i), V1')) = Names.decLUName (G, D) (* could sometimes be EName *)
			 val G' = I.Decl (G, D')
			 val _ = ind(1)  (* temporary indentation *)
			 val fmtBody = fmtExp (G', (V2, I.dot1 s), Int.max(0,imp - 1), params)
			 val _ = ind(1)
			 val fmtType = fmtExp (G, (V1', s), 0, params)
			 val _ = unind(2)
			 val pi = if (imp > 0) then "implicit_Pi" else "Pi"
		       in
				fmtBinder(pi, name, fmtType, r, fmtBody)
		       end
	  | I.No => let
		       val G' = I.Decl (G, D)
		    in
		       OMA(LFOMS(["arrow"]), [fmtExp (G, (V1, s), 0, params), fmtExp (G', (V2, I.dot1 s), 0, params)])
		    end)
    | fmtExpW (G, (I.Root (H, S), s), _, params) = let
	val l = spineLength(S)
	val out = ref ""
	val _ = if (l = 0) then
		(* no arguments *)
		out := !out ^ fmtCon (G, H, params)
	else let
		(* an application *)
		val _ = out := !out ^ "<om:OMA>" ^ nl_ind()
		(* If there are more than two explicit arguments to an infix operator,
		   the implict and the first two explicit arguments have to be wrapped in their own om:OMA element.
		   In this case, the output will not be in normal form. *)
    		val cOpt =
    			case H of
		       	   I.Const(c) => SOME c
		       	 | I.Skonst(c) => SOME c
	  		 | I.Def(c) => SOME c
		       	 | I.NSDef(c) => SOME c
		       	 | _ => NONE
      		val args = case cOpt
      		     of SOME c => (case Names.fixityLookup c
			  of Names.Fixity.Infix(_,_) => IntSyn.conDecImp (ModSyn.sgnLookup c) + 2
		           | _ => 0
		         )
		      | NONE => 0
		val _ = if args > 0 andalso (l > args)
		        then out := !out ^ "<om:OMA>" ^ nl_ind()
		        else ()
	(* print constant and arguments,
	   args is passed to fmtSpine so that fmtSpine can insert a closing tag after args arguments, 0 means no effect *)
	in out := !out ^ fmtCon (G, H, params) ^ fmtSpine (G, (S, s), args, params) ^ "</om:OMA>"
	end
      in
      	!out
      end
    | fmtExpW (G, (I.Lam(D, U), s), imp, params) = 
      let
	val (D' as I.Dec (I.VarInfo(SOME(name),r,e,i), V)) = Names.decLUName (G, D)
	val G' = I.Decl (G, D')
	val _ = ind(1)  (* temporary indentation *)
	val fmtBody = fmtExp (G', (U, I.dot1 s), Int.max(0,imp - 1), params)
	val _ = ind(1)
	val fmtType = fmtExp (G, (V, s), 0, params)
	val _ = unind(2)
	val lam = if (imp > 0) then "implicit_lambda" else "lambda"
      in
      	fmtBinder(lam, name, fmtType, r, fmtBody)
      end
    | fmtExpW (G, (I.FgnExp (csid, F), s), 0, _) = "FgnExp" (* FIX -cs Fri Jan 28 17:45:43 2005 *)

    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s), imp, params) = fmtExpW (G, Whnf.whnf (U, s), imp, params)

  (* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *)
  and fmtSpine (G, (I.Nil, _),_,_) = nl_unind()
    | fmtSpine (G, (I.SClo (S, s'), s), args, params) =
        fmtSpine (G, (S, I.comp(s',s)), args, params)
    | fmtSpine (G, (I.App(U, S), s), args, params) = let
    	(* print first argument, 0 is dummy value *)
    	val out = ref (nl() ^ fmtExp (G, (U, s), 0, params))
    	(* close application if args reaches 0 *)
    	val _ = if (args = 1) andalso (spineLength(S) > 0) then
    			out := !out ^ nl_unind() ^ "</om:OMA>"
    		else
    			()
    	(* print remaining arguments *)
      in !out ^ fmtSpine (G, (S, s), args-1, params)
      end
    	
  and fmtExpTop (G, (U, s), imp, params)
      = "<om:OMOBJ>" ^ nl_ind() ^ fmtExp (G, (U, s), imp, params) ^ nl_unind() ^ "</om:OMOBJ>"
  
  and fmtBinder(binder, name, typ, recon, scope) =
    let
    	val _ = ind(2)
    	val typ' = if recon then OM1ATTR(typ, LFOMS(["omitted"]), LFOMS(["omitted"]))
		  else typ
	val _ = unind(2)
    in
       OMBIND(LFOMS([binder]), OM1BVAR(OMV(name), MMTOMS(["type"]), typ'), scope)
    end

  and sigToStringTop(m, params) = ElemOpen("OMTHY",nil) ^ (sigToString(m, params)) ^ "</OMTHY>"
  and sigToString(m, params) = relModOMS (m, params)
  and morphToStringTop(m, params) = ElemOpen("OMMOR",nil) ^ (morphToString(m, params)) ^ "</OMMOR>"
  and morphToString(ModSyn.MorStr(c), params) = relSymOMS (c, params)
    | morphToString(ModSyn.MorView(m), params) = relModOMS (m, params)
    | morphToString(ModSyn.MorComp(mor1,mor2), params) =
      OMA(MMTOMS(["composition"]), [morphToString(mor1, params), morphToString(mor2, params)])
    | morphToString(ModSyn.MorId(m), params) =
      OMA(MMTOMS(["identity"]), [sigToStringTop(m, params)])
  and relToStringTop(rel, params) = ElemOpen("OMREL",nil) ^ (relToString(rel, params)) ^ "</OMREL>"
  and relToString(ModSyn.Rel(rel), params) = relModOMS (rel, params)
    | relToString(ModSyn.RelComp(mor,rel), params) =
      OMA(MMTOMS(["rel-mor-composition"]), [morphToString(mor, params), relToString(rel, params)])
  
  (* Printing non-modular symbol level declarations *)
  
  fun metaDataToString(NONE) = ""
    | metaDataToString(SOME (c,r)) = ElemOpen("metadata",nil) ^ nl_ind() ^
        (* ElemOpen("metadatum", [Attr("key", "origin")]) ^ r ^ ElemClose("metadatum") ^ nl() ^ *)
        ElemOpen("metadatum", [Attr("key","comment")]) ^ (escape c) ^ ElemClose("metadatum") ^ nl_unind() ^
        ElemClose("metadata") ^ nl()
  
  fun fmtSymbol(name, V, Uopt, imp, params, md) =
  	ElemOpen("constant", [Attr("name", name)]) ^ nl_ind() ^ metaDataToString md ^
  	   "<type>" ^ nl_ind() ^
  	      fmtExpTop (I.Null, (V, I.id), imp, params) ^ nl_unind() ^
  	   "</type>" ^
  	   (case Uopt
  	      of NONE => ""
  	       | SOME U =>
  	          nl() ^
  	          "<definition>" ^ nl_ind() ^
  	             fmtExpTop (I.Null, (U, I.id), imp, params) ^ nl_unind() ^
  	          "</definition>"
  	   ) ^ nl_unind() ^
  	"</constant>"

  fun fmtPresentation(cid) =
     let
  	fun fixatt(s) = Attr("fixity", s)
  	fun assocatt(s) = Attr("associativity", s)
  	fun precatt(Names.Fixity.Strength p) = Attr("precedence", Int.toString p)
  	val imp = I.conDecImp (ModSyn.sgnLookup cid)
  	val fixity = Names.fixityLookup cid
	val atts = case fixity
	       of Names.Fixity.Nonfix => nil	(* case identified by @precedence = Names.Fixity.minPrefInt *)
		| Names.Fixity.Infix(p, assoc) => [fixatt "in", assocatt (
			case assoc of
			  Names.Fixity.Left => "left"
			| Names.Fixity.Right => "right"
			| Names.Fixity.None => "none"
		), precatt p]
		| Names.Fixity.Prefix(p) => [fixatt "pre", precatt p]
		| Names.Fixity.Postfix(p) => [fixatt "post", precatt p]
    in
    	if (fixity = Names.Fixity.Nonfix andalso imp = 0)
    	then ""
        else ElemEmpty("notation", [Attr("for", "??" ^ localPath (I.conDecName(ModSyn.sgnLookup cid))),
           Attr("role", "application")] @ atts @ [Attr("implicit", Int.toString imp)])
    end

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)
     This function prints the quantifiers and abstractions only if hide = false.
  *)
  
  fun fmtConDec (I.ConDec (name, _, imp, _, V, L), params, md) =
  let
    val _ = Names.varReset IntSyn.Null
  in
    fmtSymbol(localPath name, V, NONE, imp, params, md)
  end
  | fmtConDec (I.ConDef (name, _, imp, U, V, L, _), params, md) =
  let
    val _ = Names.varReset IntSyn.Null
  in
	 fmtSymbol(localPath name, V, SOME U, imp, params, md)
  end
  | fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L), params, md) =
  let
    val _ = Names.varReset IntSyn.Null
  in
	 fmtSymbol(localPath name, V, SOME U, imp, params, md)
  end
  | fmtConDec (I.SkoDec (name, _, imp, V, L), _, _) =
      "<!-- Skipping Skolem constant " ^ localPath name ^ "-->"
  | fmtConDec (I.BlockDec (name, _, _, _), _, _) =
      "<!-- Skipping block declaration constant " ^ localPath name ^ "-->"

  (* Printing structural levels *)
  
  (* helper function to print lists *)
  fun dolist(_, nil, _) = ""
    | dolist(f, hd::nil, nl) = f hd
    | dolist(f, hd::tl, nl) = (f hd) ^ nl() ^ dolist(f, tl,nl)

  fun openToString(ModSyn.OpenDec nil, _, _) = ""
    | openToString(ModSyn.OpenDec ((c,new)::tl), strOpt, params) =
      let val old = case strOpt
           of SOME s => "??" ^ localPath (s @ (ModSyn.symName c))
            | NONE => relSymName(c, params)
      in ElemEmpty("alias", [Attr("name", localPath [new]), Attr("for", old)])
          ^ openToString(ModSyn.OpenDec tl, strOpt, params)
      end
    
  fun conDecToString (cid, params, md) = fmtConDec (ModSyn.sgnLookup cid, params, md) ^ nl() ^ fmtPresentation(cid)

  fun sigInclToString(ModSyn.SigIncl(m,opendec), params, md) =
        let val from = relModName(m, params)
        in ElemEmpty("include", [Attr("from", from)]) ^ (openToString (opendec, NONE, params)) ^ nl()
        end
  
  fun strDecToString(ModSyn.StrDec(name, _, dom, insts, opendec, _), params, md) =
     	ElemOpen("structure",
     	  [Attr("name", localPath name),
     	   Attr("from", relModName(dom,params))]) ^ metaDataToString md ^ (
           case insts of nil => ""
           | _ =>
             nl_ind() ^
               dolist(fn inst => instToString(inst, params, NONE), insts, nl) ^ 
             nl_unind()
         ) ^
      "</structure>" ^
      openToString(opendec, SOME name, params)
   | strDecToString(ModSyn.StrDef(name, _, dom, def, _), params, md) =
     ElemOpen("structure", [Attr("name", localPath name), Attr("from", relModName(dom,params))]) ^ metaDataToString md ^
     "<definition>" ^ nl_ind() ^ morphToStringTop(def, params) ^ nl_unind() ^ "</definition>" ^
     "</structure>"

  and instToString(ModSyn.ConInst(c, _, U), params, md) = 
         ElemOpen("conass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^ metaDataToString md ^
         fmtExpTop(I.Null, (U, I.id), 0, params) ^ nl_unind() ^ "</conass>"
    | instToString(ModSyn.StrInst(c, _, mor), params, md) =
         ElemOpen("strass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^ metaDataToString md ^
         morphToStringTop(mor, params) ^ nl_unind() ^ "</strass>"
    | instToString(ModSyn.InclInst(_,_,mor), params, md) =
         ElemOpen("include", nil) ^ nl_ind() ^ metaDataToString md ^
         morphToStringTop(mor, params) ^ nl_unind() ^ "</include>"

  fun caseToString(ModSyn.ConCase(c, _, U), params, md) = 
         ElemOpen("concase", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^ metaDataToString md ^ 
         fmtExpTop(I.Null, (U, I.id), 0, params) ^ nl_unind() ^ "</concase>"
    | caseToString(ModSyn.StrCase(c, _, rel), params, md) =
         ElemOpen("strcase", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^ metaDataToString md ^
         relToStringTop(rel, params) ^ nl_unind() ^ "</strcase>"
    | caseToString(ModSyn.InclCase(_,_,rel), params, md) =
         ElemOpen("include", nil) ^ nl_ind() ^ metaDataToString md ^
         relToStringTop(rel, params) ^ nl_unind() ^ "</include>"

  fun modBeginToString(mb, params : Params, md) = let
    val base = ModSyn.modDecBase mb
    val nameattr = Attr("name", localPath (ModSyn.modDecName mb))
    val nbattr = if #baseNS params = base then [nameattr] else [nameattr, Attr("base", relDocName(base, #baseNS params))]
    (* to print, e.g., from and to relative to base rather than codomain *)
    val headParams = {baseNS = base, current = #current params}
  in case mb
    of ModSyn.SigDec _ =>
      let val meta = [Attr("meta", baseLF ^ "?" ^ localPath cdLF)]
      in
         ElemOpen("theory", nbattr @ meta) ^ nl_ind() ^ metaDataToString md 
      end
    | ModSyn.ViewDec(_, _, dom, cod, _) =>
           ElemOpen("view", nbattr @ 
                          [Attr("from", relModName(dom, headParams)),
                          Attr("to", relModName(cod, headParams))]
           ) ^ nl_ind() ^ metaDataToString md
    | ModSyn.RelDec(_, _, dom, cod, mors) =>
           ElemOpen("rel", nbattr @
                          [Attr("from", relModName(dom, headParams)),
                          Attr("to", relModName(cod, headParams))]
           ) ^ nl_ind() ^ metaDataToString md ^ 
           ElemOpen("morphisms", []) ^ nl_ind() ^ dolist(fn m => morphToStringTop(m, params), mors, nl) ^ nl_unind() ^ ElemClose("morphisms") ^ nl()
  end
  fun modEndToString(ModSyn.SigDec _, _) = nl_unind() ^ "</theory>"
    | modEndToString(ModSyn.ViewDec _, _) = nl_unind() ^ "</view>"
    | modEndToString(ModSyn.RelDec _, _) = nl_unind() ^ "</rel>"
  
  fun docBeginToString(base: URI.uri, md) =
     "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
     ElemOpen("omdoc", [Attr("xmlns", "http://omdoc.org/ns"), Attr("xmlns:om", "http://www.openmath.org/OpenMath"), Attr("base", URI.uriToString base)]) ^ nl() ^ metaDataToString md ^
     "<!-- generated by Twelf -->\n"
  fun docEndToString() = "</omdoc>"
  
  (* Main interface methods *)
  
  fun printModuleBody file m params fileNameOpt =
     let
     	 fun print x = TextIO.output(file, x)
     	 fun doSym c =
     	    let val md = Comments.getCid c
          in case ModSyn.symLookup c
             of ModSyn.SymCon condec => if IntSyn.conDecQid condec = nil
                                 then print (conDecToString(c, params, md) ^ nl())
                                 else ()
              | ModSyn.SymStr strdec => if ModSyn.strDecQid strdec = nil
                                 then print (strDecToString(strdec, params, md) ^ nl())
                                 else ()
              | ModSyn.SymIncl sigincl =>
                                 print (sigInclToString(sigincl, params, md) ^ nl())
              | ModSyn.SymConInst inst => (case ModSyn.symInstOrg inst
                   of NONE => print (instToString(inst, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymStrInst inst => (case ModSyn.symInstOrg inst
                   of NONE => print (instToString(inst, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymInclInst inst => (case ModSyn.symInstOrg inst
                   of NONE => print (instToString(inst, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymConCase cas => (case ModSyn.symRelOrg cas
                   of NONE => print (caseToString(cas, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymStrCase cas => (case ModSyn.symRelOrg cas
                   of NONE => print (caseToString(cas, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymInclCase cas => (case ModSyn.symRelOrg cas
                   of NONE => print (caseToString(cas, params, md) ^ nl())
                    | SOME _ => ()
                )
              | ModSyn.SymMod(m, mdec) => printModule file m params fileNameOpt
          end
     in      
          ModSyn.sgnApp(m, doSym)
          handle ModSyn.UndefinedCid c => () (* in views not everything is defined *)
     end

  and printModule file m params fileNameOpt =
     let
     	 fun print x = TextIO.output(file, x)
     	 val mdec = ModSyn.modLookup m
     	 val bodyParams : Params = case mdec
     	   of ModSyn.SigDec(b,_) =>
     	        {baseNS = b, current = m}
     	    | ModSyn.ViewDec(_,_,_,cod,_) =>
     	        {baseNS = ModSyn.modDecBase (ModSyn.modLookup cod), current = cod}
     	    | ModSyn.RelDec(_,_,_,cod,_) =>
     	        {baseNS = ModSyn.modDecBase (ModSyn.modLookup cod), current = cod}
     	 val (fN, _) = Origins.mOriginLookup m
     	 val md = Comments.getMid m
     in
     	if fileNameOpt = SOME fN (* only print modules declared in fileName *)
     	then (
          print(modBeginToString(mdec, params, md));
          printModuleBody file m bodyParams NONE;
          print(modEndToString(mdec, params));
          print(nl() ^ nl());
          TextIO.flushOut file
      ) else ()
     end
          
  fun printDoc fileNameOpt outFile =
     let val file = TextIO.openOut outFile
         val base = case fileNameOpt
             of NONE => URI.parseURI("http://www.twelf.org/temp")
              | SOME fileName => Option.getOpt(Names.getDocNS fileName, URI.makeFileURI fileName)
         val params = {baseNS = base, current = 0}
         val md = case fileNameOpt 
           of SOME fileName => Comments.getDoc fileName
            | _ => NONE
     in (
        ind_reset();
        TextIO.output(file, docBeginToString(base, md));
        printModuleBody file 0 params fileNameOpt;
        TextIO.output(file, docEndToString());
        TextIO.closeOut file
     )
     end

end  (* functor PrintOMDoc *)
