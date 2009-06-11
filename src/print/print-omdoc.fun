(* Printing to OMDoc *)
(* Author: Florian Rabe, based on print.fun *)

functor PrintOMDoc(
   structure Whnf : WHNF
   structure Names : NAMES
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
  val baseMMT = "http://cds.omdoc.org/mmt"
  val baseLF = "http://cds.omdoc.org/lf"
  val cdMMT = ["mmt"]
  val cdLF = ["lf"]
  val cdTwelf = "twelf"
  
  (* XML and OMDoc constructors, return string *)
  fun ElemOpen'(label, attrs) = "<" ^ label ^ IDs.mkString(attrs, " ", " ", "")
  fun ElemOpen(label, attrs) = ElemOpen'(label, attrs) ^ ">"
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
  fun OMV(name) = ElemEmpty("om:OMV", [Attr("name", escape name)])
  fun OMA(func, args) = "<om:OMA>" ^ nl_ind() ^ func ^ nl() ^ IDs.mkString(args, "", nl(), "") ^ nl_unind() ^ "</om:OMA>"
  fun OMBIND(bind, vars, scope) = "<om:OMBIND>" ^ nl_ind() ^ bind ^ nl() ^ vars ^ nl() ^ scope ^ nl_unind() ^ "</om:OMBIND>"
  fun OM1ATTR(obj, key, value) = "<om:OMATTR><om:OMATP>" ^ nl_ind() ^ key ^ nl() ^ value ^ nl() ^ "</om:OMATP>" ^
                                 obj ^ nl_unind() ^ "</om:OMATTR>"
  fun OM1BVAR(name, key, value) = "<om:OMBVAR>" ^ nl_ind() ^ OM1ATTR(OMV(name), key, value) ^ nl_unind() ^ "</om:OMBVAR>"
  
  type Params = {baseFile : string list, current : IDs.mid}
  
  (* Printing references *)
  
  fun diff(nil, nil) = nil
    | diff(hd::tl, hdf::tlf) =
      if hd = hdf
      then diff(tl, tlf)
      else (List.map (fn _ => "..") tl) @ (hdf :: tlf)
  (* compute document reference (URI) relative to ! baseFile *)
  fun relDocName(doc, baseFile) = 
    let val arcs = #arcs (OS.Path.fromString doc)
    in IDs.mkString(diff( baseFile, arcs), "", "/", "")
    end
  (* compute module reference (URI) relative to ! baseFile *)
  fun relModName(m, params : Params) =
    let val dec = ModSyn.modLookup m
    in mpath(relDocName (ModSyn.modDecBase dec, #baseFile params), ModSyn.modDecName dec)
    end
  (* compute module reference (OMS) relative to ! baseFile *)
  fun relModOMS (m, params : Params) =
    let val dec = ModSyn.modLookup m
    in OMS3(relDocName (ModSyn.modDecBase dec, #baseFile params), ModSyn.modDecName dec, nil)
    end
  (* compute symbol reference (OMS) relative to ! baseFile *)
  fun relSymOMS (c, params : Params) =
    let val m = IDs.midOf c
    	val dec = ModSyn.modLookup m
        val modname = if m = #current params then nil else ModSyn.modDecName dec
        val docname = if m = 0 then "" else relDocName (ModSyn.modDecBase dec, #baseFile params)
    in OMS3(docname, modname, ModSyn.symName c)
    end

  (* Printing expressions *)
  
  (* check how many arguments there will be in an om:OMA element *)
  fun spineLength I.Nil = 0
    | spineLength (I.SClo (S, _)) = spineLength S
    | spineLength (I.App(_, S)) = 1 + (spineLength S)

  fun fmtCon (G, I.BVar(x), params) = 
      let
	val I.Dec (SOME n, _) = I.ctxDec (G, x)
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
  fun fmtExpW (G, (I.Uni(L), s), _, _) = fmtUni L
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s), imp, params) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val (D' as I.Dec (SOME(name), V1')) = Names.decLUName (G, D) (* could sometimes be EName *)
			 val G' = I.Decl (G, D')
			 val _ = ind(1)  (* temporary indentation *)
			 val fmtBody = fmtExp (G', (V2, I.dot1 s), Int.max(0,imp - 1), params)
			 val _ = ind(1)
			 val fmtType = fmtExp (G, (V1', s), 0, params)
			 val _ = unind(2)
			 val pi = if (imp > 0) then "implicit_Pi" else "Pi"
		       in
				fmtBinder(pi, name, fmtType, fmtBody)
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
	val (D' as I.Dec (SOME(name), V)) = Names.decLUName (G, D)
	val G' = I.Decl (G, D')
	val _ = ind(1)  (* temporary indentation *)
	val fmtBody = fmtExp (G', (U, I.dot1 s), Int.max(0,imp - 1), params)
	val _ = ind(1)
	val fmtType = fmtExp (G, (V, s), 0, params)
	val _ = unind(2)
	val lam = if (imp > 0) then "implicit_lambda" else "lambda"
      in
      	fmtBinder(lam, name, fmtType, fmtBody)
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
  
  and fmtBinder(binder, name, typ, scope) = OMBIND(LFOMS([binder]), OM1BVAR(name, LFOMS(["oftype"]), typ), scope)

  and morphToStringTop(m, params) = ElemOpen("om:OMMOR",nil) ^ (morphToString(m, params)) ^ "<om:OMMOR>"
  and morphToString(ModSyn.MorStr(c), params) = relSymOMS (c, params)
    | morphToString(ModSyn.MorView(m), params) = relModOMS (m, params)
    | morphToString(ModSyn.MorComp(mor1,mor2), params) =
      OMA(OMS3(baseMMT, cdMMT, ["composition"]), [morphToString(mor1, params), morphToString(mor2, params)])
  
  (* Printing non-modular symbol level declarations *)
  
  fun fmtSymbol(name, V, Uopt, imp, params) =
  	ElemOpen("constant", [Attr("name", escape name)]) ^ nl_ind() ^
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
        else ElemEmpty("notation", [Attr("for", localPath (List.map escape (I.conDecName(ModSyn.sgnLookup cid)))),
           Attr("role", "application")] @ atts @ [Attr("implicit", Int.toString imp)])
    end

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)
     This function prints the quantifiers and abstractions only if hide = false.
  *)
  
  fun fmtConDec (I.ConDec (name, _, imp, _, V, L), params) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, NONE, imp, params)
      end
    | fmtConDec (I.ConDef (name, _, imp, U, V, L, _), params) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, SOME U, imp, params)
      end
    | fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L), params) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, SOME U, imp, params)
      end
    | fmtConDec (I.SkoDec (name, _, imp, V, L), _) =
      "<!-- Skipping Skolem constant " ^ localPath name ^ "-->"
    | fmtConDec (I.BlockDec (name, _, _, _), _) =
      "<!-- Skipping block declaration constant " ^ localPath name ^ "-->"

  (* Printing structural levels *)
  
  fun openToString(ModSyn.OpenAll) = ElemEmpty("open",[])
    | openToString(ModSyn.OpenDec ((old,new)::tl))
        = ElemEmpty("open", [Attr("name", IDs.mkString(old,"",".","")), Attr("as", new)]) ^ (openToString(ModSyn.OpenDec tl))
    
  fun conDecToString (cid, params) = fmtConDec (ModSyn.sgnLookup cid, params) ^ nl() ^ fmtPresentation(cid)

  fun instToString(ModSyn.ConInst(c, U), params) = 
         ElemOpen("conass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^
         fmtExpTop(I.Null, (U, I.id), 0, params) ^ nl_unind() ^ "</conass>"
    | instToString(ModSyn.StrInst(c, mor), params) =
         ElemOpen("strass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^
         morphToStringTop(mor, params) ^ nl_unind() ^ "</strass>"

  fun modInclToString(ModSyn.SigIncl(m,opendec), params)
      = ElemOpen("include", [Attr("from", relModName(m, params))]) ^ (openToString opendec) ^ nl()
    | modInclToString(ModSyn.ViewIncl(mor), params)
      = ElemOpen("include", nil) ^ nl_ind() ^ morphToStringTop(mor, params) ^ nl_unind() ^ "</include>"
  
  fun strDecToString(ModSyn.StrDec(name, _, dom, incls, insts, _), params) =
     let 
     	fun dolist(_, nil, _) = ""
           | dolist(f, hd::nil, nl) = f hd
           | dolist(f, hd::tl, nl) = (f hd) ^ nl() ^ dolist(f, tl,nl)
     in
     	ElemOpen("structure", [Attr("name", localPath name), Attr("from", relModName(dom,params))]) ^ (
        case insts of nil => "" | _ => nl_ind() ^ dolist(fn inst => instToString(inst, params), insts, nl) ^ 
        dolist(fn incl => modInclToString(incl, params), incls, nl) ^ nl_unind()
        ) ^ "</structure>"
     end
   | strDecToString(ModSyn.StrDef(name, _, dom, def), params) =
     ElemOpen("structure", [Attr("name", localPath name), Attr("from", relModName(dom,params))]) ^
     "<definition>" ^ nl_ind() ^ morphToStringTop(def, params) ^ nl_unind() ^ "</definition>" ^
     "</structure>"

  fun modBeginToString(ModSyn.SigDec(base,name), incls, params) =
      let val (incls, meta) = case incls
                of nil => (nil, mpath(baseLF, cdLF))
                 | ModSyn.SigIncl(m,_) :: tl => (tl, relModName(m, params))
      in
         ElemOpen("theory", [Attr("name", localPath name), Attr("meta", meta)]) ^ nl_ind() ^
         IDs.mkString(List.map (fn x => modInclToString(x, params)) incls, "", nl(), nl())
      end
    | modBeginToString(ModSyn.ViewDec(base, name, dom, cod), incls, params) =
        ElemOpen("view", [Attr("name", localPath name),
                          Attr("from", relModName(dom, params)),
                          Attr("to", relModName(cod, params))]
        ) ^ nl_ind() ^ IDs.mkString(List.map (fn incl => modInclToString(incl, params)) incls, "", nl(), nl())
               
  fun modEndToString(ModSyn.SigDec _, _) = nl_unind() ^ "</theory>"
    | modEndToString(ModSyn.ViewDec _, _) = nl_unind() ^ "</view>"
  
  fun docBeginToString(base) =
     "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
     "<omdoc " ^           
     "xmlns=\"http://omdoc.org/ns\" " ^
     "xmlns:om=\"http://www.openmath.org/OpenMath\" " ^
     "uri=\"" ^ base ^ "\"" ^
     ">\n"
  fun docEndToString() = "</omdoc>"
  
  (* Main interface methods *)
    
  fun printModule file m baseFile =
     let
     	 fun print x = (TextIO.output(file, x); TextIO.flushOut file)
     	 val mdec = ModSyn.modLookup m
     	 val incls = ModSyn.modInclLookup m
     	 val params : Params = {baseFile = baseFile, current = m}
     in
     	if #arcs (OS.Path.fromString (ModSyn.modDecBase mdec)) = baseFile (* only print modules from the base file *)
     	then (
          print(modBeginToString(mdec, incls, params));
          ModSyn.sgnApp(m, fn c =>
           (case ModSyn.symLookup c
             of ModSyn.SymCon condec => if IntSyn.conDecQid condec = nil
                                 then print (conDecToString(c, params) ^ nl())
                                 else ()
              | ModSyn.SymStr strdec => if ModSyn.strDecQid strdec = nil
                                 then print (strDecToString(strdec, params) ^ nl())
                                 else ()
              | ModSyn.SymConInst inst => print (instToString(inst, params) ^ nl())
              | ModSyn.SymStrInst inst => print (instToString(inst, params) ^ nl())
           ) handle ModSyn.UndefinedCid _ => ()  (* @FR in views not everything is defined *)
          );
          print(modEndToString(mdec, params));
          print(nl() ^ nl());
          TextIO.flushOut file
        ) else ()
     end

  fun toFile filename =
     let val file = TextIO.openOut (filename)
         val ModSyn.SigDec(f,_) = ModSyn.modLookup(0)
         val baseFile = #arcs (OS.Path.fromString f)
     in (
        ind_reset();
        TextIO.output(file, docBeginToString(f));
        ModSyn.modApp(fn m => printModule file m baseFile);
        TextIO.output(file, docEndToString());
        TextIO.closeOut file
     )
     end

end  (* functor PrintOMDoc *)
