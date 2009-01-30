(* Printing to OMDoc *)
(* Author: Florian Rabe, based on print.fun *)

functor PrintOMDoc(
   structure Whnf : WHNF
   structure Names : NAMES
)
  : PRINT_OMDOC =
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
  fun OMS(cd,name) = OMS3("", cd, name)
  fun OMV(name) = ElemEmpty("om:OMV", [Attr("name", escape name)])
  fun OMA(func, args) = "<om:OMA>" ^ nl_ind() ^ func ^ nl() ^ IDs.mkString(args, "", nl(), "") ^ nl_unind() ^ "</om:OMA>"
  fun OMBIND(bind, vars, scope) = "<om:OMBIND>" ^ nl_ind() ^ bind ^ nl() ^ vars ^ nl() ^ scope ^ nl_unind() ^ "</om:OMBIND>"
  fun OM1ATTR(obj, key, value) = "<om:OMATTR><om:OMATP>" ^ nl_ind() ^ key ^ nl() ^ value ^ nl() ^ "</om:OMATP>" ^
                                 obj ^ nl_unind() ^ "</om:OMATTR>"
  fun OM1BVAR(name, key, value) = "<om:OMBVAR>" ^ nl_ind() ^ OM1ATTR(OMV(name), key, value) ^ nl_unind() ^ "</om:OMBVAR>"
  
  (* Printing expressions *)
  
  (* check how many arguments there will be in an om:OMA element *)
  fun spineLength I.Nil = 0
    | spineLength (I.SClo (S, _)) = spineLength S
    | spineLength (I.App(_, S)) = 1 + (spineLength S)

  fun fmtCid(cid) = OMS(ModSyn.modName (IDs.midOf cid), ModSyn.symName cid)
  fun fmtCon (G, I.BVar(x)) = 
      let
	val I.Dec (SOME n, _) = I.ctxDec (G, x)
      in 
	OMV(n)
      end
    | fmtCon (G, I.Const(cid)) = fmtCid cid
    | fmtCon (G, I.Def(cid)) = fmtCid cid
    | fmtCon (G, I.NSDef(cid)) = fmtCid cid
    | fmtCon (G, I.FgnConst (csid, condec)) = "FgnConst"  (* FIX -cs Fri Jan 28 17:45:35 2005*)
    (* I.Skonst, I.FVar cases should be impossible *)

  fun fmtUni (I.Type) = OMS(cdLF, ["type"])
    | fmtUni (I.Kind) = OMS(cdLF, ["kind"])

  (* fmtExpW (G, (U, s)) = fmt
     format the expression U[s].
     Invariants:
       G is a "printing context" (names in it are unique, but
            types may be incorrect) approximating G'
       G'' |- U : V   G' |- s : G''  (so  G' |- U[s] : V[s])
       (U,s) in whnf
  *)
  fun fmtExpW (G, (I.Uni(L), s), _) = fmtUni L
    | fmtExpW (G, (I.Pi((D as I.Dec(_,V1),P),V2), s), imp) =
      (case P (* if Pi is dependent but anonymous, invent name here *)
	 of I.Maybe => let
			 val (D' as I.Dec (SOME(name), V1')) = Names.decLUName (G, D) (* could sometimes be EName *)
			 val G' = I.Decl (G, D')
			 val _ = ind(1)  (* temporary indentation *)
			 val fmtBody = fmtExp (G', (V2, I.dot1 s), Int.max(0,imp - 1))
			 val _ = ind(1)
			 val fmtType = fmtExp (G, (V1', s), 0)
			 val _ = unind(2)
			 val pi = if (imp > 0) then "implicit_Pi" else "Pi"
		       in
				fmtBinder(pi, name, fmtType, fmtBody)
		       end
	  | I.No => let
		       val G' = I.Decl (G, D)
		    in
		       OMA(OMS(cdLF, ["arrow"]), [fmtExp (G, (V1, s), 0), fmtExp (G', (V2, I.dot1 s), 0)])
		    end)
    | fmtExpW (G, (I.Root (H, S), s), _) = let
	val l = spineLength(S)
	val out = ref ""
	val _ = if (l = 0) then
		(* no arguments *)
		out := !out ^ fmtCon (G, H)
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
	in out := !out ^ fmtCon (G, H) ^ fmtSpine (G, (S, s), args) ^ "</om:OMA>"
	end
      in
      	!out
      end
    | fmtExpW (G, (I.Lam(D, U), s), imp) = 
      let
	val (D' as I.Dec (SOME(name), V)) = Names.decLUName (G, D)
	val G' = I.Decl (G, D')
	val _ = ind(1)  (* temporary indentation *)
	val fmtBody = fmtExp (G', (U, I.dot1 s), Int.max(0,imp - 1))
	val _ = ind(1)
	val fmtType = fmtExp (G, (V, s), 0)
	val _ = unind(2)
	val lam = if (imp > 0) then "implicit_lambda" else "lambda"
      in
      	fmtBinder(lam, name, fmtType, fmtBody)
      end
    | fmtExpW (G, (I.FgnExp (csid, F), s), 0) = "FgnExp" (* FIX -cs Fri Jan 28 17:45:43 2005 *)

    (* I.EClo, I.Redex, I.EVar not possible *)

  and fmtExp (G, (U, s), imp) = fmtExpW (G, Whnf.whnf (U, s), imp)

  (* fmtSpine (G, (S, s), args) = fmts
     format spine S[s] at printing depth d, printing length l, in printing
     context G which approximates G', where G' |- S[s] is valid
     args is the number of arguments after which </om:OMA> must be inserted, no effect if negative
  *)
  and fmtSpine (G, (I.Nil, _),_) = nl_unind()
    | fmtSpine (G, (I.SClo (S, s'), s), args) =
        fmtSpine (G, (S, I.comp(s',s)), args)
    | fmtSpine (G, (I.App(U, S), s), args) = let
    	(* print first argument, 0 is dummy value *)
    	val out = ref (nl() ^ fmtExp (G, (U, s), 0))
    	(* close application if args reaches 0 *)
    	val _ = if (args = 1) andalso (spineLength(S) > 0) then
    			out := !out ^ nl_unind() ^ "</om:OMA>"
    		else
    			()
    	(* print remaining arguments *)
      in !out ^ fmtSpine (G, (S, s), args-1)
      end
    	
  and fmtExpTop (G, (U, s), imp) = "<om:OMOBJ>" ^ nl_ind() ^ fmtExp (G, (U, s), imp) ^ nl_unind() ^ "</om:OMOBJ>"
  
  and fmtBinder(binder, name, typ, scope) = OMBIND(OMS(cdLF, [binder]), OM1BVAR(name, OMS(cdLF, ["oftype"]), typ), scope)
  
  (* Printing non-modular symbol level declarations *)
  
  fun fmtSymbol(name, V, Uopt, imp) =
  	ElemOpen("constant", [Attr("name", escape name)]) ^ nl_ind() ^
  	   "<type>" ^ nl_ind() ^
  	      fmtExpTop (I.Null, (V, I.id), imp) ^ nl_unind() ^
  	   "</type>" ^
  	   (case Uopt
  	      of NONE => ""
  	       | SOME U =>
  	          nl() ^
  	          "<definition>" ^ nl_ind() ^
  	             fmtExpTop (I.Null, (U, I.id), imp) ^ nl_unind() ^
  	          "</definition>"
  	   ) ^ nl_unind() ^
  	"</constant>"

  fun fmtPresentation(cid) =
     let
  	val imp = I.conDecImp (ModSyn.sgnLookup cid)
  	val fixity = Names.fixityLookup cid
	val fixString = case fixity
	       of Names.Fixity.Nonfix => "prefix"	(* case identified by @precedence = Names.Fixity.minPrefInt *)
		| Names.Fixity.Infix(_, assoc) => (
			case assoc of
			  Names.Fixity.Left => "leftassoc"
			| Names.Fixity.Right => "rightassoc"
			| Names.Fixity.None => "infix"
		)
		| Names.Fixity.Prefix(_) => "prefix"
		| Names.Fixity.Postfix(_) => "postfix"
        val name = localPath (List.map escape (I.conDecName(ModSyn.sgnLookup cid)))
    in
        ElemEmpty("notation",
	  [Attr("for", name),
	   Attr("precedence", Int.toString (Names.Fixity.precToIntAsc(fixity))),
	   Attr("fixity", fixString),
	   Attr("implicit", Int.toString imp)]
        )
    end

  (* fmtConDec (condec) = fmt
     formats a constant declaration (which must be closed and in normal form)
     This function prints the quantifiers and abstractions only if hide = false.
  *)
  
  fun fmtConDec (I.ConDec (name, _, imp, _, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, NONE, imp)
      end
    | fmtConDec (I.ConDef (name, _, imp, U, V, L, _)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, SOME U, imp)
      end
    | fmtConDec (I.AbbrevDef (name, parent, imp, U, V, L)) =
      let
	val _ = Names.varReset IntSyn.Null
      in
	fmtSymbol(localPath name, V, SOME U, imp)
      end
    | fmtConDec (I.SkoDec (name, _, imp, V, L)) =
      "<!-- Skipping Skolem constant " ^ localPath name ^ "-->"
    | fmtConDec (I.BlockDec (name, _, _, _)) =
      "<!-- Skipping block declaration constant " ^ localPath name ^ "-->"


  (* Printing module level declarations *)
  
  fun docBeginToString() =
           "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ^
           "<omdoc " ^
           "xmlns=\"http://omdoc.org/omdoc\" " ^
           "xmlns:om=\"http://www.openmath.org/OpenMath\"" ^
           ">\n"
  fun docEndToString() = "</omdoc>"
  
  fun modInclToString(m) = ElemEmpty("import", [Attr("from", mpath("", ModSyn.modName m))]) ^ nl()
  
  fun modBeginToString(ModSyn.SigDec name, incls) =
      let val (incls, meta) = case incls
                of nil => (nil, mpath(baseLF, cdLF))
                 | m :: tl => (tl, mpath("", ModSyn.modName m))
      in
         ElemOpen("theory", [Attr("name", localPath name), Attr("meta", meta)]) ^ nl_ind() ^
         IDs.mkString(List.map (fn x => modInclToString x) incls, "", nl(), nl())
      end
    | modBeginToString(ModSyn.ViewDec(name, dom, cod), _) =
        ElemOpen("view", [Attr("name", localPath name),
                          Attr("from", mpath("", ModSyn.modName dom)),
                          Attr("to", mpath("", ModSyn.modName cod))]
        ) ^ nl_ind()
               
  fun modEndToString(ModSyn.SigDec _) = nl_unind() ^ "</theory>"
    | modEndToString(ModSyn.ViewDec _) = nl_unind() ^ "</view>"
  
  fun expToString (G, U, imp) = fmtExp (G, (U, I.id), imp)  
  
  fun morphToString(ModSyn.MorStr(c)) = fmtCid c
    | morphToString(ModSyn.MorView(m)) = OMS3("", ModSyn.modName m, nil)
    | morphToString(ModSyn.MorComp(mor1,mor2)) =
      OMA(OMS3(baseMMT, cdMMT, ["composition"]), [morphToString(mor1), morphToString(mor2)])
      
  fun instToString(ModSyn.ConInst(c, U)) = 
         ElemOpen("conass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^
         fmtExpTop(I.Null, (U, I.id), 0) ^ nl_unind() ^ "</conass>"
    | instToString(ModSyn.StrInst(c, mor)) =
         ElemOpen("strass", [Attr("name", localPath (ModSyn.symName c))]) ^ nl_ind() ^
         morphToString(mor) ^ nl_unind() ^ "</strass>"

  fun strDecToString(ModSyn.StrDec(name, _, dom, insts)) =
     let 
     	fun dolist(_, nil, _) = ""
           | dolist(f, hd::nil, nl) = f hd
           | dolist(f, hd::tl, nl) = (f hd) ^ nl() ^ dolist(f, tl,nl)
     in
     	ElemOpen("structure", [Attr("name", localPath name), Attr("from", mpath("", ModSyn.modName dom))]) ^ (
        case insts of nil => "" | _ => nl_ind() ^ dolist(instToString, insts, nl) ^ nl_unind()
        ) ^ "</structure>"
     end
   | strDecToString(ModSyn.StrDef(name, _, dom, def)) =
     ElemOpen("structure", [Attr("name", localPath name), Attr("from", mpath("",ModSyn.modName dom))]) ^
     "<definition>" ^ nl_ind() ^ morphToString def ^ nl_unind() ^ "</definition>" ^
     "</structure>"

  fun conDecToString cid = fmtConDec (ModSyn.sgnLookup cid) ^ nl() ^ fmtPresentation(cid)

  (* Main interface methods *)
    
  fun printModule print flush m =
     let
     	 val mdec = ModSyn.modLookup m
     	 val incls = ModSyn.modInclLookup m
     in (
        print(modBeginToString(mdec, incls));
        ModSyn.sgnApp(m, fn c => (
           (case ModSyn.symLookup c
             of ModSyn.SymCon condec => if IntSyn.conDecQid condec = nil
                                 then print (conDecToString c ^ nl())
                                 else ()
              | ModSyn.SymStr strdec => if ModSyn.strDecQid strdec = nil
                                 then print (strDecToString strdec ^ nl())
                                 else ()
              | ModSyn.SymConInst inst => print (instToString inst ^ nl())
              | ModSyn.SymStrInst inst => print (instToString inst ^ nl())
           ) handle ModSyn.UndefinedCid _ => ()  (* @FR in views not everything is defined *)
           ;
           flush()
           )
        );
        print(modEndToString mdec)
     )
     end

  fun printDoc filename =
     let val file = TextIO.openOut (filename)
     in (
        ind_reset();
        TextIO.output(file, docBeginToString());
        ModSyn.modApp(fn m => (
           printModule (fn x => (TextIO.output(file, x))) (fn () => TextIO.flushOut file) m;
           TextIO.output(file, nl() ^ nl())
        ));
        TextIO.output(file, docEndToString());
        TextIO.closeOut file
     )
     end

end  (* functor PrintOMDoc *)
