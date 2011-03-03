(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow *)
(* Modified: Brigitte Pientka, Roberto Virga *)

functor Twelf
  (structure Global : GLOBAL
   structure Timers : TIMERS
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
   structure Lexer : LEXER
   (*! sharing Lexer.Paths = Paths !*)
     (*! structure Parsing : PARSING !*)
     (*! sharing Lexer = Lexer !*)
   structure Parser : PARSER
     sharing Parser.Names = Names
     (*! sharing Parser.ExtSyn.Paths = Paths !*)
   structure TypeCheck : TYPECHECK
   structure Strict : STRICT
   (*! sharing Strict.IntSyn = IntSyn' !*)
   (*! sharing Strict.Paths = Paths !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn' !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn' !*)
   structure ReconTerm : RECON_TERM
   (*! sharing ReconTerm.IntSyn = IntSyn' !*)
   (*! sharing ReconTerm.Paths = Paths !*)
     sharing type ReconTerm.term = Parser.ExtSyn.term
     (* sharing type ReconTerm.Paths.occConDec = Origins.Paths.occConDec *)
   structure ReconConDec : RECON_CONDEC
   (*! sharing ReconConDec.IntSyn = IntSyn' !*)
   (*! sharing ReconConDec.Paths = Paths !*)
     sharing type ReconConDec.condec = Parser.ExtConDec.condec
   structure ReconQuery : RECON_QUERY
   structure ModeTable : MODETABLE
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure ModeCheck : MODECHECK
   (*! sharing ModeCheck.IntSyn = IntSyn' !*)
   (*! sharing ModeCheck.ModeSyn = ModeSyn !*)
   (*! sharing ModeCheck.Paths = Paths !*)
   structure ReconMode : RECON_MODE
   (*! sharing ReconMode.ModeSyn = ModeSyn !*)
     (*! sharing ReconMode.Paths = Paths !*)
     sharing type ReconMode.modedec = Parser.ExtModes.modedec
   structure ModePrint : MODEPRINT
   (*! sharing ModePrint.ModeSyn = ModeSyn !*)
   structure ModeDec : MODEDEC
   (*! sharing ModeDec.ModeSyn = ModeSyn !*)
     (*! sharing ModeDec.Paths = Paths !*)

   structure StyleCheck : STYLECHECK

   structure Unique : UNIQUE
   (*! sharing Unique.ModeSyn = ModeSyn !*)
   structure UniqueTable : MODETABLE

   structure Cover : COVER
   (*! sharing Cover.IntSyn = IntSyn' !*)
   (*! sharing Cover.ModeSyn = ModeSyn !*)

   structure Converter : CONVERTER
   (*! sharing Converter.IntSyn = IntSyn' !*)
   (*! sharing Converter.Tomega = Tomega !*)
   structure TomegaPrint : TOMEGAPRINT
   (*! sharing TomegaPrint.IntSyn = IntSyn' !*)
   (*! sharing TomegaPrint.Tomega = Tomega !*)
   structure TomegaCoverage : TOMEGACOVERAGE
   (*! sharing TomegaCoverage.IntSyn = IntSyn' !*)
   (*! sharing TomegaCoverage.Tomega = Tomega !*)
   structure TomegaTypeCheck : TOMEGATYPECHECK
   (*! sharing TomegaTypeCheck.IntSyn = IntSyn' !*)
   (*! sharing TomegaTypeCheck.Tomega = Tomega !*)

   structure Total : TOTAL
   (*! sharing Total.IntSyn = IntSyn' !*)

   structure Reduces : REDUCES
   (*! sharing Reduces.IntSyn = IntSyn' !*)

   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)
   structure IndexSkolem : INDEX
   (*! sharing IndexSkolem.IntSyn = IntSyn' !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)
   (*! structure CompSyn' : COMPSYN !*)
   (*! sharing CompSyn'.IntSyn = IntSyn' !*)
   structure Compile : COMPILE
   (*! sharing Compile.IntSyn = IntSyn' !*)
   (*! sharing Compile.CompSyn = CompSyn' !*)
   structure AbsMachine : ABSMACHINE
   (*! sharing AbsMachine.IntSyn = IntSyn' !*)
   (*! sharing AbsMachine.CompSyn = CompSyn' !*)
   (*! structure TableParam : TABLEPARAM !*)
   structure Tabled : TABLED
   (*! sharing Tabled.IntSyn = IntSyn' !*)
   (*! sharing Tabled.CompSyn = CompSyn' !*)
   structure Solve : SOLVE
   (*! sharing Solve.IntSyn = IntSyn' !*)
     sharing type Solve.ExtQuery.query = Parser.ExtQuery.query
     sharing type Solve.ExtQuery.define = Parser.ExtQuery.define
     sharing type Solve.ExtQuery.solve = Parser.ExtQuery.solve
   structure Fquery : FQUERY
   (*! sharing Fquery.IntSyn = IntSyn' !*)
     sharing type Fquery.ExtQuery.query = Parser.ExtQuery.query
     sharing type Fquery.ExtQuery.define = Parser.ExtQuery.define
     sharing type Fquery.ExtQuery.solve = Parser.ExtQuery.solve
	     (*! sharing Solve.Paths = Paths !*)
   structure ThmSyn : THMSYN
   (*! sharing ThmSyn.Paths = Paths !*)
   structure Thm : THM
     sharing Thm.ThmSyn = ThmSyn
     (*! sharing Thm.Paths = Paths !*)
   structure ReconThm : RECON_THM
     sharing ReconThm.ThmSyn = ThmSyn
     (*! sharing ReconThm.Paths = Paths !*)
     (*! sharing ReconThm.ThmSyn.ModeSyn = ModeSyn !*)
     sharing type ReconThm.tdecl = Parser.ThmExtSyn.tdecl
     sharing type ReconThm.rdecl = Parser.ThmExtSyn.rdecl (* -bp *)
     sharing type ReconThm.tableddecl = Parser.ThmExtSyn.tableddecl (* -bp *)
     sharing type ReconThm.keepTabledecl = Parser.ThmExtSyn.keepTabledecl (* -bp *)
     sharing type ReconThm.wdecl = Parser.ThmExtSyn.wdecl 
     sharing type ReconThm.theorem = Parser.ThmExtSyn.theorem
     sharing type ReconThm.theoremdec = Parser.ThmExtSyn.theoremdec 
     sharing type ReconThm.prove = Parser.ThmExtSyn.prove
     sharing type ReconThm.establish = Parser.ThmExtSyn.establish
     sharing type ReconThm.assert = Parser.ThmExtSyn.assert
   structure ThmPrint : THMPRINT
     sharing ThmPrint.ThmSyn = ThmSyn

   structure TabledSyn : TABLEDSYN
   (*! sharing TabledSyn.IntSyn = IntSyn' !*)

   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   structure Worldify : WORLDIFY
   structure WorldPrint : WORLDPRINT
   (*! sharing WorldPrint.Tomega = Tomega !*)

   structure ReconModule : RECON_MODULE
     sharing type ReconModule.strdec = Parser.ModExtSyn.strdec
     sharing type ReconModule.syminst = Parser.ModExtSyn.syminst
     sharing type ReconModule.symcase = Parser.ModExtSyn.symcase
     sharing type ReconModule.modbegin = Parser.ModExtSyn.modbegin
     sharing type ReconModule.sigincl = Parser.ModExtSyn.sigincl
     sharing type ReconModule.read = Parser.ModExtSyn.read
     sharing type ReconModule.namespace = Parser.ModExtSyn.namespace
   structure MetaGlobal : METAGLOBAL
   (*! structure FunSyn : FUNSYN !*)
   (*! sharing FunSyn.IntSyn = IntSyn' !*)
   structure Skolem : SKOLEM
   (*! sharing Skolem.IntSyn = IntSyn' !*)
   structure Prover : PROVER
   (*! sharing Prover.IntSyn = IntSyn' !*)
   structure ClausePrint : CLAUSEPRINT
   (*! sharing ClausePrint.IntSyn = IntSyn' !*)

   structure Trace : TRACE

   structure PrintTeX : PRINT
   (*! sharing PrintTeX.IntSyn = IntSyn' !*)
   structure ClausePrintTeX : CLAUSEPRINT
   (*! sharing ClausePrintTeX.IntSyn = IntSyn' !*)
   structure PrintOMDoc : PRINTFILE
   
   structure CSManager : CS_MANAGER
   (*! sharing CSManager.IntSyn = IntSyn' !*)
     sharing CSManager.Fixity = Names.Fixity
   (*! sharing CSManager.ModeSyn = ModeSyn !*)
    
   structure CSInstaller : CS_INSTALLER
   structure Compat : COMPAT
   structure UnknownExn : UNKNOWN_EXN

   structure Msg : MSG
     )
 :> TWELF =
struct

  local
    (*! structure IntSyn = IntSyn' !*)
    structure S = Parser.Stream

    fun msg s = Msg.message s
    fun chmsg n s = Global.chMessage n s msg

    fun fileOpenMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => msg ("[Loading file " ^ fileName ^ " ...")
	    | _ => msg ("[Opening file " ^ fileName ^ "]\n"))

    fun fileCloseMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => msg ("]\n")
	    | _ => msg ("[Closing file " ^ fileName ^ "]\n"))

    (* result of a computation *)
    datatype 'a Result = Value of 'a | Exception of exn

    (* val withOpenIn : string -> (TextIO.instream -> 'a) -> 'a *)
    (* withOpenIn fileName (fn instream => body) = x
       opens fileName for input to obtain instream and evaluates body.
       The file is closed during normal and abnormal exit of body.
    *)
    fun withOpenIn (fileName) (scope) =
	let
	  val instream = TextIO.openIn fileName
	  val _ = fileOpenMsg (fileName)
	  val result = Value (scope instream) handle exn => Exception (exn)
	  val _ = fileCloseMsg (fileName)
	  val _ = TextIO.closeIn instream
	in
	  case result
	    of Value (x) => x
	     | Exception (exn) => raise exn
	end

    (* evarInstToString Xs = msg
       formats instantiated EVars as a substitution.
       Abbreviate as empty string if chatter level is < 3.
    *)
    fun evarInstToString (Xs) =
	if !Global.chatter >= 3
	  then Print.evarInstToString (Xs)
	else ""

    (* expToString (G, U) = msg
       formats expression as a string.
       Abbreviate as empty string if chatter level is < 3.
    *)
    fun expToString GU =
	if !Global.chatter >= 3
	  then Print.expToString GU
	else ""

    fun printProgTeX () =
        (msg "\\begin{bigcode}\n";
	 ClausePrintTeX.printSgn ();
	 msg "\\end{bigcode}\n")

    fun printSgnTeX () =
        (msg "\\begin{bigcode}\n";
	 PrintTeX.printSgn ();
         msg "\\end{bigcode}\n")

    (* status ::= OK | ABORT  is the return status of various operations *)
    datatype Status = OK | ABORT

    fun abort chlev (msg) = (chmsg chlev (fn () => msg); ABORT)
    fun abortFileMsg chlev (fileName, msg) = abort chlev (fileName ^ ":" ^ msg ^ "\n")

    fun abortIO (fileName, {cause = OS.SysErr (m, _), function = f, name = n}) =
	(msg ("IO Error on file " ^ fileName ^ ":\n" ^ m ^ "\n");
	 ABORT)
      | abortIO (fileName, {function = f, ...}) =
	(msg ("IO Error on file " ^ fileName ^ " from function "
		       ^ f ^ "\n");
	 ABORT)

    (* should move to paths, or into the prover module... but not here! -cs *)
    fun joinregion (r, nil) = r
      | joinregion (r, r' :: rs) = 
          joinregion (Paths.join (r, r'), rs)

    fun joinregions (r::rs) = joinregion (r, rs)

    fun constraintsMsg (cnstrL) =
        "Typing ambiguous -- unresolved constraints\n" ^ Print.cnstrsToString cnstrL

    (* val handleExceptions : int -> string -> ('a -> Status) -> 'a -> Status *)
    (* handleExceptions chlev filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued if chatter level is greater or equal to chlev.
       Unrecognized exceptions are re-raised.
    *)
    fun handleExceptions chlev fileName (f:'a -> Status) (x:'a) =
	(f x
	 handle ReconTerm.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ReconConDec.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ReconQuery.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ReconMode.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ReconThm.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | TypeCheck.Error (msg) => abort 0 ("Double-checking types fails: " ^ msg ^ "\n"
						^ "This indicates a bug in Twelf.\n")
	      | Abstract.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Constraints.Error (cnstrL) => abortFileMsg chlev (fileName, constraintsMsg cnstrL) (* put back in because it may be raised by the module system -fr Mar 09 *)
	      | Total.Error (msg) => abort chlev (msg ^ "\n")	(* Total includes filename *)
	      | Reduces.Error (msg) => abort chlev (msg ^ "\n") (* Reduces includes filename *)
              | Compile.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Thm.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ModeTable.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | ModeCheck.Error (msg) => abort chlev (msg ^ "\n") (* ModeCheck includes filename *)
	      | ModeDec.Error (msg) => abortFileMsg chlev (fileName, msg)
              | Unique.Error (msg) => abortFileMsg chlev (fileName, msg)
              | Cover.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Parsing.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Lexer.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | IntSyn.Error (msg) => abort chlev ("Signature error: " ^ msg ^ "\n")
	      | Names.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Names.MissingModule(_,_,msg) => abortFileMsg chlev (fileName, msg) (* special case of Names.Error -fr *)
	      (* - IO.Io not supported in polyML ABP - 4/20/03 -- assuming it's supported by now -fr 2010 *)
 	      | IO.Io (ioError) => abortIO (fileName, ioError)
	      | Solve.AbortQuery (msg) => abortFileMsg chlev (fileName, msg)
	      | ThmSyn.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Prover.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | Strict.Error (msg) => abortFileMsg chlev (fileName, msg)
              | Subordinate.Error (msg) => abortFileMsg chlev (fileName, msg)
	      | WorldSyn.Error (msg) => abort chlev (msg ^ "\n") (* includes filename *)
	      | Worldify.Error (msg) => abort chlev (msg ^ "\n") (* includes filename *)
              | ModSyn.Error (msg) => abortFileMsg chlev (fileName, msg)       (* -fr *)
              | ReconModule.Error (msg) => abortFileMsg chlev (fileName, msg)  (* -fr *)
              | Elab.Error (msg) => abortFileMsg chlev (fileName, msg)         (* -fr *)
	      | Converter.Error (msg) => abortFileMsg chlev (fileName, msg)
              | CSManager.Error (msg) => abort chlev ("Constraint Solver Manager error: " ^ msg ^ "\n")
	      | exn => (abort 0 (UnknownExn.unknownExn exn); raise exn))

    (* better: lookup shortest undefined prefix -fr *)
    fun undeclaredIdentifier qid = IDs.foldQName qid
    
    fun installConst fromCS (cid, fileNameocOpt) =
        let
          val _ = Origins.installOrigin (cid, fileNameocOpt)
          val _ = Index.install fromCS (IntSyn.Const cid)
          val _ = IndexSkolem.install fromCS (IntSyn.Const cid)
          val _ = (Timers.time Timers.compiling Compile.install) fromCS cid
          val _ = (Timers.time Timers.subordinate Subordinate.install) cid
          val _ = (Timers.time Timers.subordinate Subordinate.installDef) cid
        in
          ()
        end

    (* installConDec fromCS (conDec, ocOpt)
       installs the constant declaration conDec which originates at ocOpt
       in various global tables, including the global signature.
       Note: if fromCS = FromCS then the declaration comes from a Constraint
       Solver and some limitations on the types are lifted.
    *)
    fun installConDec fromCS (conDec, fileNameocOpt as (fileName, ocOpt), r) =
	let
	  val _ = (Timers.time Timers.modes ModeCheck.checkD) (conDec, fileName, ocOpt)
	  val cid = ModSyn.sgnAddC conDec
	  val _ = Names.installNameC (cid, NONE, IntSyn.conDecName conDec)
	          handle Names.Error(msg) => raise Names.Error(Paths.wrap(r, msg))
	  val _ = installConst fromCS (cid, fileNameocOpt)
	          handle Subordinate.Error (msg) => raise Subordinate.Error (Paths.wrap (r, msg))
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	  val _ = Comments.install cid
	  val _ =  if !Global.style >= 1 then StyleCheck.checkConDec cid else ()
	in 
	  cid
	end
    
    fun installBlockDec fromCS (conDec, fileNameocOpt as (fileName, ocOpt), r) =
	let
	  val cid = ModSyn.sgnAddC conDec
	  val _ = Names.installNameC (cid, NONE, IntSyn.conDecName conDec)
	          handle Names.Error(msg) => raise Names.Error(Paths.wrap(r, msg))
	  (* val _ = Origins.installOrigin (cid, fileNameocOpt) *)
	  val _ = (Timers.time Timers.subordinate Subordinate.installBlock) cid
	          handle Subordinate.Error (msg) => raise Subordinate.Error (Paths.wrap (r, msg))
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end
    
    fun installStrDec(strDec, r) =
       let
          val c : IDs.cid = ModSyn.structAddC(strDec)
          val _ = Names.installNameC(c, NONE, ModSyn.strDecName strDec)
                  handle Names.Error(msg) => raise Names.Error(Paths.wrap(r, msg))
       in
       	  c
       end

    (* auxiliary method shared by install1(StrDec _) (then byStr = SOME s) and install1(ModIncl _) (then byStr = NONE) *)
    fun installOpen(dom : IDs.mid, opens : (IDs.cid * string) list, origin : IDs.cid, r) = (
       	  List.map (fn (c,new) =>
             let
                val c' = case ModSyn.symLookup origin
                  of ModSyn.SymStr _ => if IDs.midOf c = dom
          	     then valOf (ModSyn.structMapLookup(origin,c))
                     else raise Names.Error("cannot open included symbol " ^ ModSyn.symFoldName c)
                   | _ => c
             in
                Names.installNameC(c', SOME origin, [new])
             end
          ) opens;
          ()
    ) handle Names.Error(msg) => raise Names.Error(Paths.wrap(r,msg))

    fun installCSMDec (conDec, optFixity, mdecL) = 
	let
	  val _ = ModeCheck.checkD (conDec, "%use", NONE)
          (* put a more reasonable region here? -kw *)
	  val cid = installConDec IntSyn.FromCS (conDec, ("", NONE), Paths.Reg (0,0))
	  val _ = if !Global.chatter >= 3
		  then msg (Print.conDecToString (conDec) ^ "\n")
		  else ()
	  val _ = (case optFixity
		     of SOME(fixity) =>
			  (Names.installFixity (cid, fixity);
                           if !Global.chatter >= 3
                             then msg ((if !Global.chatter >= 4 then "%" else "")
                                         ^ Names.Fixity.toString fixity ^ " "
                                         ^ IntSyn.conDecFoldName (ModSyn.sgnLookup cid) ^ ".\n")
                           else ())
		      | NONE => ())
	  val _ = List.app (fn mdec => ModeTable.installMmode (cid, mdec)) mdecL
	in
	  cid
	end

    val _ = CSManager.setInstallFN (installCSMDec)
 
    fun cidToString a = IntSyn.conDecFoldName (ModSyn.sgnLookup a)

    fun invalidate uninstallFun cids msg =
        let
	  val uninstalledCids = List.filter (fn a => uninstallFun a) cids
	  val _ = case uninstalledCids
                    of nil => ()
                     | _ => chmsg 4
		            (fn () => "Invalidated " ^ msg ^ " properties of families"
			     ^ List.foldr (fn (a,s) => " " ^ cidToString a ^ s) "\n"
			     uninstalledCids)
	in
	  ()
	end

    (* reset () = () clears all global tables, including the signature *)
    fun reset () = (ModSyn.reset (); (* -fr *)
                    Names.reset ();
                    Origins.reset ();
		    ModeTable.reset ();
		    UniqueTable.reset (); (* -fp Wed Mar  9 20:24:45 2005 *)
		    Index.reset (); 
		    IndexSkolem.reset ();
		    Subordinate.reset ();
		    Total.reset ();	(* -fp *)
		    WorldSyn.reset ();	(* -fp *)
		    Reduces.reset ();	(* -bp *)
		    TabledSyn.reset ();	(* -bp *)
		    FunSyn.labelReset ();
		    CompSyn.sProgReset (); (* necessary? -fp; yes - bp*)
		    CompSyn.detTableReset (); (*  -bp *)
		    Compile.sProgReset (); (* resetting substitution trees *)
                    CSManager.resetSolvers ();
                    Comments.reset() (* preserved comments -fr *)
		    )

    (* like Names.MissingModule, used to load a module on demand
       may be raised only by a case of install1 that has not changed the global state yet *)
    exception GetModule of URI.uri * string * string
    (* install goes through a stream and calls install1 on every declarations *)
    fun install(fileName, stream) = 
      let fun inst s' = inst' ((Timers.time Timers.parsing S.expose) s')
          and inst'(S.Empty) = OK
            | inst'(S.Cons (decr, s')) =
              let val _ = tryInstall1 (fileName, decr, nil)
              in inst s'
              end
      in
      	  case inst stream
	    of ABORT => ABORT
	     | OK => if ModSyn.onToplevel()
	             then OK else raise ModSyn.Error("expected declaration or `}', found end of input")
      end

    (* tryInstall1(fileName, decr, missing)
       repeatedly calls install1(fileName, decr) until the exception GetModule is not thrown anymore
       if GetModule is thrown, it loads the missing module before retrying
       missing is the list of all missing modules to detect cycles (the length of missing is one less than the number of currently active nested calls of tryInstall1)
    *)
    and tryInstall1(fileName, decr as (_,r), missing) =
       install1(fileName, decr)
       handle GetModule(ns,modname,err) =>
       case List.find (fn x => x = (ns,modname)) missing
         (* check for cycle *)
         of SOME (n,m) => raise Names.Error("missing module " ^ m ^ " in namespace " ^ URI.uriToString n ^
                       " cannot be found (dependency cycle or faulty catalog entry)")
          | _ => let
          (* no cycle *)
          val _ = chmsg 3 (fn () => "%% loading missing module " ^ modname ^ " in namespace " ^ URI.uriToString ns ^ "\n")
          val dir = OS.Path.dir fileName (* base directory of current elf file *)
          (* name must be in Unix syntax and relative to dir (absolute name not done yet) *)
          val url = URI.toFilePath ns
          (* the currently open signatures, i.e., M1, M1.M2, ..., M1.....Mn depend
             on the missing module, so their name entries are removed temporarily and saved *)
          val cdec = ModSyn.modLookup(ModSyn.currentMod())
          val cnames = (URI.uriToString (ModSyn.modDecBase cdec)) :: (ModSyn.modDecName cdec)
          fun init(hd::nil) = nil | init(hd::tl) = hd::(init tl)
          fun saveEntries(ns::nil) = nil
            | saveEntries(names) = (names, Names.uninstallName(0, names)) :: (saveEntries(init names))
          val entries = saveEntries cnames (* entry of M1.....Mn first, entry of M1 last *)
          (* save current context of ModSyn and Names *)
          val _ = Names.pushContext() (* @FR: redundant *)
          val _ = ModSyn.pushContext()
          (* save the current line info *)
          val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
          (* load the missing module - for now: assume it's a file and load the whole file
             - all loaded modules are inserted into the toplevel signature right before M1 so that the mids are not in logical order anymore
             - the cid of M1 is increased accordingly so that the cids are still in logical order
          *)
          val _ = chmsg 3 (fn () => "%% loading from " ^ url ^ "\n")
          val stat = loadFile url
          val _ = if stat = ABORT
                  then raise ModSyn.Error("Error in dynamically loaded module " ^ URI.uriToString ns) else ()
          (* restore previous file name and line info *)
          val _ = ReconTerm.resetErrors fileName;
          val _ = Paths.setLinesInfo(valOf (Origins.linesInfoLookup fileName))
          (* restore the context of ModSyn and Names, the former returns the new cid of M1 *)
          val cnew = ModSyn.popContext()
          val _ = Names.popContext()
          (* restore the (updated) name entries for the modules M1.....Mi
             update: cnew replaces the old cid of M1 (nil-case) and the old origins of M1....Mi for i>1 (tl-cases) *)
          fun restoreEntries((names, _)::nil) = Names.installName(0, cnew, NONE, names)
            | restoreEntries((names,(c,_))::tl) = (
                Names.installName(0, c, SOME cnew, names);
                restoreEntries tl
              )
          val _ = (restoreEntries entries)
                  handle Names.Error(msg) => raise Names.Error(Paths.wrap(r,
                   "dynamically loaded modules were installed correctly, but one of them overwrote the name of a currently open module: " ^ msg))
          val _ = chmsg 3 (fn () => "%% loaded missing module " ^ modname ^ " in namespace " ^ URI.uriToString ns ^ "; retrying\n")
       in
          (* finally retry *)
          tryInstall1(fileName, decr, (ns,modname) :: missing)
       end

    (* install1 installs one declaration, effects global state, may raise standard exceptions *)
    and install1 (fileName, (Parser.ConDec condec, r)) =
        (* Constant declarations c : V, c : V = U plus variations *)
        (let
	   val (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName,r), false)
	   fun icd (SOME (conDec as IntSyn.BlockDec _)) = 
       let
        (* allocate new cid. *)
          val cid = installBlockDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
       in
          ()
       end
      | icd (SOME (conDec)) =
        let
		 (* names are assigned in ReconConDec *)
		 (* val conDec' = nameConDec (conDec) *)
		 (* should print here, not in ReconConDec *)
		 (* allocate new cid after checking modes! *)
          val cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
       in
          ()
       end
      | icd (NONE) = (* anonymous definition for type-checking *)
	       ()
	 in
	   icd optConDec
	 end
	 handle Constraints.Error (eqns) =>
	        raise ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))

      | install1 (fileName, (Parser.AbbrevDec condec, r)) =
        (* Abbreviations %abbrev c = U and %abbrev c : V = U *)
        (let
	  val (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName,r), true)
	  fun icd (SOME(conDec)) =
	      let
		  (* names are assigned in ReconConDec *)
		  (* val conDec' = nameConDec (conDec) *)
		  (* should print here, not in ReconConDec *)
		  (* allocate new cid after checking modes! *)
		  val cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)
	      in
		()
	      end
	    | icd (NONE) = (* anonymous definition for type-checking *)
	        ()
	in
	  icd optConDec
	end
        handle Constraints.Error (eqns) =>
	       raise ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))

      | install1 (fileName, (Parser.ClauseDec condec, r)) =
	(* Clauses %clause c = U or %clause c : V = U or %clause c : V *)
	(* these are like definitions, but entered into the program table *)
	(let
	   (* val _ = print "%clause " *)
	   val (optConDec, ocOpt) = ReconConDec.condecToConDec (condec, Paths.Loc (fileName, r), false)
	   fun icd (SOME (conDec)) =
	       let
		 val cid = installConDec IntSyn.Clause (conDec, (fileName, ocOpt), r)
	       in
		 ()
	       end
	     | icd NONE = (* anonymous definition for type-checking: ignore %clause *)
	       ()
	 in
	   icd optConDec
	 end
	 handle Constraints.Error (eqns) =>
	        raise ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))
	   
      (* Solve declarations %solve c : A *)
      | install1 (fileName, (Parser.Solve (defines, solve), r)) =
	(let
	  val conDecL = Solve.solve (defines, solve, Paths.Loc (fileName, r))
	                handle Solve.AbortQuery (msg) =>
			 raise Solve.AbortQuery (Paths.wrap (r, msg))
          fun icd (conDec, ocOpt) =
          (let
	     (* should print here, not in ReconQuery *)
	     (* allocate new cid after checking modes! *)
	     (* allocate cid after strictness has been checked! *)
	     val cid = installConDec IntSyn.Ordinary (conDec, (fileName, ocOpt), r)

	   in
	     ()
	   end)
         in
           List.app icd conDecL
         end
         handle Constraints.Error (eqns) =>
	        raise ReconTerm.Error (Paths.wrap (r, constraintsMsg eqns)))

      (* %query <expected> <try> A or %query <expected> <try> X : A *)
      | install1 (fileName, (Parser.Query(expected,try,query), r)) =
        (* Solve.query might raise Solve.AbortQuery (msg) *)
	(Solve.query ((expected, try, query), Paths.Loc (fileName, r))
	 handle Solve.AbortQuery (msg)
	        => raise Solve.AbortQuery (Paths.wrap (r, msg)))
      (* %fquery <expected> <try> A or %fquery <expected> <try> X : A *)
      | install1 (fileName, (Parser.FQuery (query), r)) =
        (* Solve.query might raise Fquery.AbortQuery (msg) *)
	(Fquery.run (query, Paths.Loc (fileName, r))
	 handle Fquery.AbortQuery (msg)
	        => raise Fquery.AbortQuery (Paths.wrap (r, msg)))

      (* %queryTabled <expected> <try> A or %query <expected> <try> X : A *)
      | install1 (fileName, (Parser.Querytabled(numSol, try,query), r)) =
        (* Solve.query might raise Solve.AbortQuery (msg) *)
	(Solve.querytabled ((numSol, try, query), Paths.Loc (fileName, r))
	 handle Solve.AbortQuery (msg)
	        => raise Solve.AbortQuery (Paths.wrap (r, msg)))

      (* %trustme <decl> *)
      | install1 (fileName, (Parser.TrustMe(dec,r'), r)) =
	let 
          val _ = if not (!Global.unsafe)
		    then raise Thm.Error("%trustme not safe: Toggle `unsafe' flag")
		  else ()
	  val _ = chmsg 3 (fn () => "[%trustme ...\n")
	  val _ = case handleExceptions 4 fileName (fn args => (install1 args; OK)) (fileName, (dec, r))
		   of OK => chmsg 3 (fn () => "trustme subject succeeded\n")
		    | ABORT => chmsg 3 (fn () => "trustme subject failed; continuing\n")
          val _ = chmsg 3 (fn () => "%]\n")
	in
	  ()
	end

      (* %subord (<qid> <qid>) ... *)
      | install1 (fileName, (Parser.SubordDec (qidpairs), r)) = 
        let
          fun toCid qid =
              case Names.nameLookupC qid
                of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier " ^ undeclaredIdentifier qid ^
                                              " in subord declaration"))
                 | SOME cid => cid
          val cidpairs = List.map (fn (qid1, qid2) => (toCid qid1, toCid qid2)) qidpairs
                     handle Names.Error (msg) =>
		       raise Names.Error (Paths.wrap (r, msg))
	  val _ = List.app Subordinate.addSubord cidpairs
    	            handle Subordinate.Error (msg) =>
		      raise Subordinate.Error (Paths.wrap (r, msg))
        in
          if !Global.chatter >= 3
          then msg ("%subord"
                      ^ List.foldr 
			    (fn ((a1, a2), s) => " (" ^ 
				IntSyn.conDecFoldName (ModSyn.sgnLookup a1) ^ " " ^
				IntSyn.conDecFoldName (ModSyn.sgnLookup a2) ^ ")" ^ s) ".\n" cidpairs)
          else ()
        end

      (* %freeze <qid> ... *)
      | install1 (fileName, (Parser.FreezeDec (qids), r)) = 
        let
          fun toCid qid =
              case Names.nameLookupC qid
                of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier "
                                              ^ undeclaredIdentifier qid ^ " in freeze declaration"))
                 | SOME cid => cid
          val cids = List.map toCid qids
                     handle Names.Error (msg) =>
		       raise Names.Error (Paths.wrap (r, msg))
	  val frozen = Subordinate.freeze cids
	               handle Subordinate.Error (msg) =>
			 raise Subordinate.Error (Paths.wrap (r, msg))
        in
	  (* Subordinate.installFrozen cids *)
          if !Global.chatter >= 3
          then msg ("%freeze"
                      ^ List.foldr (fn (a, s) => " " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ s) ".\n" cids)
          else ();
	  if !Global.chatter >= 4
	    then msg ("Frozen:" ^ List.foldr (fn (a,s) => " " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ s) "\n" frozen)
	  else ()
        end

      (* %thaw <qid> ... *)
      | install1 (fileName, (Parser.ThawDec (qids), r)) =
	let
	  val _ = if not (!Global.unsafe)
		    then raise ThmSyn.Error "%thaw not safe: Toggle `unsafe' flag"
	          else ()
	  fun toCid qid =
	      case Names.nameLookupC qid
		of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier "
					      ^ undeclaredIdentifier qid ^ " in thaw declaration"))
		 | SOME cid => cid
	  val cids = List.map toCid qids
	             handle Names.Error (msg) => raise Names.Error (Paths.wrap (r, msg))
	  val thawed = Subordinate.thaw cids
			handle Subordinate.Error(msg) =>
			  raise Subordinate.Error (Paths.wrap (r, msg))
	  val _ = if !Global.chatter >= 3
		    then msg ("%thaw"
				^ List.foldr (fn (a, s) => " " ^ cidToString a ^ s) ".\n" cids)
		  else ()
	  val _ = if !Global.chatter >= 4
		    then msg ("Thawed" ^ List.foldr (fn (a,s) => " " ^ cidToString a ^ s) "\n" thawed)
		  else ()
          (* invalidate prior meta-theoretic properteis of signatures *)
	  (* exempt only %mode [incremental], %covers [not stored] *)
          val _ = invalidate WorldSyn.uninstall thawed "world"
          val _ = invalidate Thm.uninstallTerminates thawed "termination"
	  val _ = invalidate Thm.uninstallReduces thawed "reduction"
          val _ = invalidate UniqueTable.uninstallMode thawed "uniqueness"
          val _ = invalidate Total.uninstall thawed "totality"
	in
	  ()
	end

      (* %deterministic <qid> ... *)
      | install1 (fileName, (Parser.DeterministicDec (qids), r)) = 
        let
          fun toCid qid =
              case Names.nameLookupC qid
                of NONE =>
                    raise Names.Error (Paths.wrap (r, "Undeclared identifier "
                                       ^ undeclaredIdentifier qid ^ " in deterministic declaration"))
                 | SOME cid => cid
          fun insertCid cid = CompSyn.detTableInsert (cid, true)
          val cids = List.map toCid qids
                       handle Names.Error (msg) =>
                         raise Names.Error (Paths.wrap (r, msg))
        in
          List.map insertCid cids;
          if !Global.chatter >= 3
          then msg ((if !Global.chatter >= 4 then "%" else "")
                      ^ "%deterministic"
                      ^ List.foldr (fn (a, s) => " " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ s) ".\n" cids)
          else ()
        end

      (* %compile <qids> *) (* -ABP 4/4/03 *)
      | install1 (fileName, (Parser.Compile (qids), r)) = 
        let
          fun toCid qid =
              case Names.nameLookupC qid
                of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier "
                                              ^ undeclaredIdentifier qid ^ " in compile assertion"))
                 | SOME cid => cid
          val cids = List.map toCid qids
                     handle Names.Error (msg) => raise Names.Error (Paths.wrap (r, msg))

	  (* MOVED -- ABP 4/4/03 *)
	  (* ******************************************* *)
	  fun checkFreeOut nil = ()
	    | checkFreeOut (a :: La) =
	      let 
		val SOME ms = ModeTable.modeLookup a
	        val _ = ModeCheck.checkFreeOut (a, ms)
	      in
		checkFreeOut La 
	      end

	  val _ = checkFreeOut cids
	  (* ******************************************* *)

	  val (lemma, projs, sels) = Converter.installPrg cids
	  val P = Tomega.lemmaDef lemma
	  val F = Converter.convertFor cids
	  val _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F))

	  fun f cid = IntSyn.conDecFoldName (ModSyn.sgnLookup cid)

	  val _ = if !Global.chatter >= 2 
		    then msg ("\n" ^ 
				TomegaPrint.funToString ((map f cids, projs), P)
				^ "\n")
		  else ()

          val _ = if !Global.chatter >= 3
		    then msg ((if !Global.chatter >= 4 then "%" else "")
				^ "%compile"
				^ List.foldr (fn (a, s) => " " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a) ^ s) ".\n" cids)
		  else ()
        in
	  ()
        end

      (* Fixity declaration for operator precedence parsing *)
      | install1 (fileName, (Parser.FixDec ((qid,r),fixity), _)) =
        (case Names.nameLookupC qid
           of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier "
                                         ^ undeclaredIdentifier qid ^ " in fixity declaration"))
            | SOME cid => (Names.installFixity (cid, fixity);
                           if !Global.chatter >= 3
                             then msg ((if !Global.chatter >= 4 then "%" else "")
                                         ^ Names.Fixity.toString fixity ^ " "
                                         ^ IntSyn.conDecFoldName (ModSyn.sgnLookup cid) ^ ".\n")
                           else ())
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Name preference declaration for printing *)
      | install1 (fileName, (Parser.NamePref ((qid,r), namePref), _)) =
        (case Names.nameLookupC qid
           of NONE => raise Names.Error (Paths.wrap (r, "Undeclared identifier "
                                         ^ undeclaredIdentifier qid ^ " in name preference"))
            | SOME cid => Names.installNamePref (cid, namePref)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Mode declaration *)
      | install1 (fileName, (Parser.ModeDec mterms, r)) =
	let 
	  val mdecs = List.map ReconMode.modeToMode mterms
          val _ = ReconTerm.checkErrors (r)
	  val _ = List.app (fn (mdec as (a, _), r) =>
			    case ModeTable.modeLookup a
			      of NONE => ()
			       | SOME _ =>
				 if Subordinate.frozen [a]
				   then raise ModeTable.Error (Paths.wrap (r, "Cannot redeclare mode for frozen constant " ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)))
				 else ())
		  mdecs
	  val _ = List.app (fn (mdec as (a, _), r) => 
	                    (case (IntSyn.conDecStatus (ModSyn.sgnLookup a))
			       of IntSyn.Normal => ModeTable.installMode mdec
			        | _ => raise ModeTable.Error "Cannot declare modes for foreign constants")
			    handle ModeTable.Error (msg) => raise ModeTable.Error (Paths.wrap (r, msg)))
	          mdecs
          val _ = List.app (fn mdec => ModeDec.checkPure mdec) mdecs
	  val _ = List.app (fn (mdec, r) => ModeCheck.checkMode mdec (* exception comes with location *)
			    handle ModeCheck.Error (msg) => raise ModeCheck.Error (msg))
	          mdecs
	  val _ = if !Global.chatter >= 3 
		    then msg ("%mode " ^ ModePrint.modesToString
				           (List.map (fn (mdec, r) => mdec) mdecs)
					 ^ ".\n")
		  else ()		   
	in
	  ()
	end

      (* Unique declaration *)
      | install1 (fileName, (Parser.UniqueDec mterms, r)) =
	let
	  val mdecs = List.map ReconMode.modeToMode mterms
	  val _ = ReconTerm.checkErrors (r)
          (* convert all UniqueTable.Error to Unique.Error *)
	  val _ = List.app (fn (mdec as (a, _), r) => 
	                    (case (IntSyn.conDecStatus (ModSyn.sgnLookup a))
			       of IntSyn.Normal => UniqueTable.installMode mdec
			        | _ => raise UniqueTable.Error "Cannot declare modes for foreign constants")
			    handle UniqueTable.Error (msg) => raise Unique.Error (Paths.wrap (r, msg)))
	          mdecs
          (* Timing added to coverage --- fix !!! -fp Sun Aug 17 12:17:51 2003 *)
          val _ = List.app (fn (mdec, r) => (Timers.time Timers.coverage Unique.checkUnique) mdec
                                handle Unique.Error (msg) => raise Unique.Error (Paths.wrap (r, msg)))
	          mdecs
          (* %unique does not auto-freeze, since family must already be frozen *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%unique " ^ ModePrint.modesToString
				           (List.map (fn (mdec, r) => mdec) mdecs)
					 ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Coverage declaration *)
      | install1 (fileName, (Parser.CoversDec mterms, r)) =
	let
	  val mdecs = List.map ReconMode.modeToMode mterms
          val _ = ReconTerm.checkErrors (r)
          val _ = List.app (fn mdec => ModeDec.checkPure mdec) mdecs   (* MERGE Fri Aug 22 13:43:12 2003 -cs *)
	  val _ = List.app (fn (mdec, r) => (Timers.time Timers.coverage Cover.checkCovers) mdec
			    handle Cover.Error (msg) => raise Cover.Error (Paths.wrap (r, msg)))
	          mdecs
	  val _ = if !Global.chatter >= 3
		    then msg ("%covers " ^ ModePrint.modesToString
				             (List.map (fn (mdec, r) => mdec) mdecs)
					   ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Total declaration *)
      | install1 (fileName, (Parser.TotalDec lterm, r)) =
        (* time activities separately in total.fun *)
	let
        (* Mon Dec  2 17:20:18 2002 -fp *)
        (* coverage checker appears to be safe now *)
	  (*
	  val _ = if not (!Global.unsafe)
		    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "%total not safe: Toggle `unsafe' flag"))
	          else ()
          *)
	  val (T, rrs as (r,rs)) = ReconThm.tdeclTotDecl lterm
	  val La = Thm.installTotal (T, rrs)

(* ******************************************* *)
(*  Temporarily disabled -- cs Thu Oct 30 12:46:44 2003 
	  fun checkFreeOut nil = ()
	    | checkFreeOut (a :: La) =
	      let 
		val SOME ms = ModeTable.modeLookup a
	        val _ = ModeCheck.checkFreeOut (a, ms)
	      in
		checkFreeOut La 
	      end
	  val _ = checkFreeOut La
	  val (lemma, projs, sels) = Converter.installPrg La


	  (* ABP 2/28/03 -- factoring *)
	  val _ = if (!Global.chatter >= 4) then print ("[Factoring ...") else ()
	  val P = Redundant.convert (Tomega.lemmaDef lemma)
	  val _ = if (!Global.chatter >= 4) then print ("]\n") else ()

	  val F = Converter.convertFor La

	  val _ = if !Global.chatter >= 2
		    then print (TomegaPrint.funToString ((map (fn (cid) => IntSyn.conDecName (ModSyn.sgnLookup cid)) La,
							  projs), P) ^ "\n")
		  else ()

	  val _ = TomegaTypeCheck.checkPrg (IntSyn.Null, (P, F))
	      
	  val result1 = (TomegaCoverage.coverageCheckPrg (WorldSyn.lookup (hd La), IntSyn.Null, P); NONE) 
	                handle TomegaCoverage.Error msg => SOME msg


(*	val result1 = NONE *)

 	  fun covererror (SOME msg1, msg2) = raise Cover.Error (Paths.wrap (r, "Functional and relational coverage checker report coverage error:\n[Functional] " 
									    ^ msg1 ^ "\n[Relational] " ^ msg2))
	    | covererror (NONE, msg2)      = raise Cover.Error (Paths.wrap (r, "Functional coverage succeeds, relationals fails:\n[Relational] " ^ msg2))

 ******************************************* *)

	  val _ = map Total.install La	(* pre-install for recursive checking *)
	  val _ = map Total.checkFam La
	          handle Total.Error (msg) => raise Total.Error (msg) (* include region and file *)
		       | Cover.Error (msg) => raise Cover.Error (Paths.wrap (r, msg))
(*		       | Cover.Error (msg) => covererror (result1, msg)  disabled -cs Thu Jan 29 16:35:13 2004 *)
		       | Reduces.Error (msg) => raise Reduces.Error (msg) (* includes filename *)
		       | Subordinate.Error (msg) => raise Subordinate.Error (Paths.wrap (r, msg))
(*	  val _ = case (result1) 
	            of NONE => ()
		     | SOME msg => raise Cover.Error (Paths.wrap (r, "Relational coverage succeeds, funcational fails:\n This indicates a bug in the functional checker.\n[Functional] " ^ msg))
*)
          (* %total does not auto-freeze, since the predicate must already be frozen *)
	  val _ = if !Global.chatter >= 3
		    then msg ("%total " ^ ThmPrint.tDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Termination declaration *)
      | install1 (fileName, (Parser.TerminatesDec lterm, _)) =
	let
	  val (T, rrs as (r, rs)) = ReconThm.tdeclTotDecl lterm
	  val ThmSyn.TDecl (_, ThmSyn.Callpats(callpats)) = T
          (* allow re-declaration since safe? *)
	  (* Thu Mar 10 13:45:42 2005 -fp *)
	  (*
	  val _ = ListPair.app (fn ((a, _), r) =>
			    if Subordinate.frozen [a]
			      andalso ((Order.selLookup a; true) handle Order.Error _ => false)
			    then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare termination order for frozen constant "
						   ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)))
			    else ())
	          (callpats, rs)
          *)
	  val La = Thm.installTerminates (T, rrs)
  	  val _ = map (Timers.time Timers.terminate Reduces.checkFam) La   
	  val _ = if !Global.autoFreeze then (Subordinate.freeze La; ()) else ()
	  val _ = if !Global.chatter >= 3 
		    then msg ("%terminates " ^ ThmPrint.tDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

        (* -bp *)
	(* Reduces declaration *)
      | install1 (fileName, (Parser.ReducesDec lterm, _)) =
	let
	  val (R, rrs as (r, rs)) = ReconThm.rdeclTorDecl lterm 
	  val ThmSyn.RDecl (_, ThmSyn.Callpats(callpats)) = R
	  (* allow re-declaration since safe? *)
	  (* Thu Mar 10 14:06:13 2005 -fp *)
	  (*
	  val _ = ListPair.app (fn ((a, _), r) =>
			    if Subordinate.frozen [a]
			      andalso ((Order.selLookupROrder a; true) handle Order.Error _ => false)
			    then raise Total.Error (fileName ^ ":"
                                       ^ Paths.wrap (r, "Cannot redeclare reduction order for frozen constant "
						   ^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)))
			    else ())
	          (callpats, rs)
          *)
	  val La = Thm.installReduces (R, rrs)
	  (*  -bp6/12/99.   *)
	  val _ = map (Timers.time Timers.terminate Reduces.checkFamReduction) La
	  val _ = if !Global.autoFreeze then (Subordinate.freeze La; ()) else ()
	  val _ = if !Global.chatter >= 3 
		    then msg ("%reduces " ^ ThmPrint.rDeclToString R ^ ".\n")
		  else ()
	in
	  ()
	end

	(* Tabled declaration *)
      | install1 (fileName, (Parser.TabledDec tdecl, _)) =
	let
	  val (T,r) = ReconThm.tableddeclTotabledDecl tdecl 
	  val La = Thm.installTabled T
	  (*  -bp6/12/99.   *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%tabled " ^ ThmPrint.tabledDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

      (* %keepTable declaration *)
      | install1 (fileName, (Parser.KeepTableDec tdecl, _)) =
	let
	  val (T,r) = ReconThm.keepTabledeclToktDecl tdecl 
	  val La = Thm.installKeepTable T
	  val _ = if !Global.chatter >= 3 
		    then msg ("%keeptabled " ^ ThmPrint.keepTableDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Theorem declaration *)
      | install1 (fileName, (Parser.TheoremDec tdec, r)) =
	let 
	  val Tdec = ReconThm.theoremDecToTheoremDec tdec
          val _ = ReconTerm.checkErrors (r)
	  val (GBs, E as IntSyn.ConDec (name, _, k, _, V, L)) = ThmSyn.theoremDecToConDec (Tdec, r)
	  val _ = FunSyn.labelReset ()
	  val _ = List.foldr (fn ((G1, G2), k) => FunSyn.labelAdd 
			    (FunSyn.LabelDec (Int.toString k, FunSyn.ctxToList G1, FunSyn.ctxToList G2))) 0 GBs
								       
	  val cid = installConDec IntSyn.Ordinary (E, (fileName, NONE), r)
	  val MS = ThmSyn.theoremDecToModeSpine (Tdec, r)
	  val _ = ModeTable.installMode (cid, MS)
	  val _ = if !Global.chatter >= 3
		    then msg ("%theorem " ^ Print.conDecToString E ^ "\n")
		  else ()
	in
	  ()
	end

      (* Prove declaration *)
      | install1 (fileName, (Parser.ProveDec lterm, r)) =
	let
	  val (ThmSyn.PDecl (depth, T), rrs) = ReconThm.proveToProve lterm 
	  val La = Thm.installTerminates (T, rrs)  (* La is the list of type constants *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%prove " ^ (Int.toString depth) ^ " " ^
				       (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	  val _ = Prover.init (depth, La)
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => msg ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]

	  val _ = Prover.auto ()
	          handle Prover.Error msg
		         => raise Prover.Error (Paths.wrap (joinregion rrs, msg)) (* times itself *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%QED\n")
		  else ()
		    
	in
	  (Prover.install (fn E => installConDec IntSyn.Ordinary (E, (fileName, NONE), r));
	   Skolem.install La) 
	end 

      (* Establish declaration *)
      | install1 (fileName, (Parser.EstablishDec lterm, r)) =
        let 
	  val (ThmSyn.PDecl (depth, T), rrs) = ReconThm.establishToEstablish lterm 
	  val La = Thm.installTerminates (T, rrs)  (* La is the list of type constants *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%prove " ^ (Int.toString depth) ^ " " ^
				       (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	  val _ = Prover.init (depth, La)
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => msg ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]

	  val _ = Prover.auto () handle Prover.Error msg => raise Prover.Error (Paths.wrap (joinregion rrs, msg)) (* times itself *)
		    
	in
	  Prover.install (fn E => installConDec IntSyn.Ordinary (E, (fileName, NONE), r))
	end 

      (* Assert declaration *)
      | install1 (fileName, (Parser.AssertDec aterm, _)) =
	let 
	  val _ = if not (!Global.unsafe)
		    then raise ThmSyn.Error "%assert not safe: Toggle `unsafe' flag"
	          else ()
	  val (cp as ThmSyn.Callpats (L), rrs) = ReconThm.assertToAssert aterm 
	  val La = map (fn (c, P) => c) L  (* La is the list of type constants *)
	  val _ = if !Global.chatter >= 3 
		    then msg ("%assert " ^ (ThmPrint.callpatsToString cp) ^ ".\n")
		  else ()
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => msg ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeTable.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]
	in
	  Skolem.install La
	end

      | install1 (fileName, (Parser.WorldDec wdecl, _)) =
	let
	  val (ThmSyn.WDecl (qids, cp as ThmSyn.Callpats cpa), rs) =
	         ReconThm.wdeclTowDecl wdecl
	  val _ = ListPair.app (fn ((a, _), r) =>
		    if Subordinate.frozen [a]
		      then raise WorldSyn.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "Cannot declare worlds for frozen family "
								^ IntSyn.conDecFoldName (ModSyn.sgnLookup a)))
		    else ())
	         (cpa, rs)
	  val W = Tomega.Worlds
	      (List.map (fn qid => case Names.nameLookupC qid
			            of NONE => raise Names.Error ("Undeclared label "
                                         ^ undeclaredIdentifier qid
                                         ^ ".")
                                     | SOME cid => cid)
	      qids)
	  val _ = List.app (fn (a, _) => WorldSyn.install (a, W)) cpa
	          handle WorldSyn.Error (msg)
		         (* error location inaccurate here *)
		         => raise WorldSyn.Error (Paths.wrapLoc (Paths.Loc (fileName, joinregions rs), msg))
	  val _ = if !Global.autoFreeze
		    then (Subordinate.freeze (List.map (fn (a, _) => a) cpa) ; ())
		  else ()
	  val _ = if !Global.chatter >= 3 
		    then msg ("%worlds " ^ WorldPrint.worldsToString W ^ " "
				^ ThmPrint.callpatsToString cp ^ ".\n")
		  else ()
	in
	  (Timers.time Timers.worlds (map (fn (a, _) => WorldSyn.worldcheck W a)) cpa ; ()
	   (*if !Global.doubleCheck 
	     then (map (fn (a,_) => Worldify.worldify a) cpa; ())
	   else  ()  --cs Sat Aug 27 22:04:29 2005 *))
	  
	end
      | install1 (fileName, (Parser.Use name, r)) =
        (if ModSyn.onToplevel()
           then CSManager.useSolver (name)
           else raise ModSyn.Error (Paths.wrap (r, "%use declaration needs to be at top level"))
        )

      (* cases for the module system *)
      | install1 (fileName, declr as (Parser.ModBegin modBegin, r)) =
           let
               val dec = ReconModule.modbeginToModDec(modBegin, Paths.Loc(fileName, r))
                         handle Names.MissingModule(ns,m,s) => raise GetModule(ns,m,s)
               val _ = Elab.checkModBegin dec
                       handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
               val ancmids = List.map #1 (ModSyn.getScope())
               val parent = hd ancmids
               val c = ModSyn.modOpen(dec)
                       handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg))
               (* copy parent's subordination relation, no exceptions should be possible *)
               val _ = case dec
                  of ModSyn.SigDec _ => Subordinate.installInclude parent
                     | _ =>  ()
               (* new module has qualified name M_1.....M_n and cid c
                  for i=1,...,n, name M_i.....M_n resolves to c in signature M_1.....M_{i-1}
                     (M_1.....M_0 means toplevel signature)
                     origin is given by cid of M_i in M_1.....M_{i-1}, no origin for i=n *)
               fun init(hd::nil) = nil | init(hd::tl) = hd::(init tl)
               val origins = NONE :: (List.map (fn m => SOME (ModSyn.midToCid m)) (init ancmids))
               fun doNames(mid::mids, names, c, org::orgs) =
                   let val names' = if mid = 0 then (URI.uriToString (ModSyn.modDecBase dec)) :: names else names
                   in (Names.installName(mid, c, org, names')
                       handle Names.Error msg => raise Names.Error(Paths.wrap(r, msg));
                       doNames(mids, tl names, c, orgs)
                   ) end
                 | doNames(nil,nil,c,nil) = ()
               val _ = doNames(rev ancmids, ModSyn.modDecName dec, c, rev origins)
               val _ = Origins.installMOrigin(ModSyn.cidToMid c, (fileName,r))
               val _ = Comments.install c
           in
             chmsg 3 (fn () => Print.modBeginToString(dec) ^ "\n")
           end
      | install1 (fileName, declr as (Parser.ModEnd, r)) =
          let
             val m = ModSyn.currentMod()
             val _ = Elab.checkModEnd m
                     handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
             val (fN,rb) = Origins.mOriginLookup m  (* fN = fileName *)
          in
             ModSyn.modClose()
             handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg));
             Origins.installMOrigin(m, (fileName, Paths.join(rb,r)));
             chmsg 3 (fn () => Print.modEndToString(ModSyn.modLookup m) ^ "\n\n")
          end
      | install1 (fileName, declr as (Parser.StrDec strdec, r)) =
         let
            (* reconstruct, check, and install structure declaration
               only structural checking at this point, full type-checking only in Elab.flatten below *)
            val strDec = ReconModule.strdecToStrDec (strdec, Paths.Loc (fileName,r))
                         handle Names.MissingModule(ns,m,s) => raise GetModule(ns,m,s)
            val _ = ReconTerm.checkErrors(r)
            val NewStrDec = Elab.checkStrDec(strDec)
                    handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
            val c = installStrDec (NewStrDec, r)
            (* print it *)
            val prefix = if (! Global.printFlat) then "% " else ""
            val _ = if ! Global.chatter >= 3 then msg (prefix ^ Print.strDecToString NewStrDec ^ "\n") else ()
            (* called by Elab.flatten when d is generated by applying instantiation to constant c' *)
            fun callbackInstallConDec(c' : IDs.cid, d : IntSyn.ConDec) =
               let
               	  (* normalize, double check, and install generated declaration *)
               	  val dn = Whnf.normalizeConDec d
		  val _ = if ! Global.doubleCheck then TypeCheck.checkConDec dn else ()
                  val c = installConDec IntSyn.Ordinary (dn, (fileName, NONE), r)
                  (* copy fixity, name preferences, mode from the original to the new declaration *)
                  val _ = case Names.fixityLookup c'
                            of Names.Fixity.Nonfix => ()
                             | fix => Names.installFixity(c, fix)
                  val _ = case Names.namePrefLookup c'
                            of NONE => ()
                             | SOME pref => Names.installNamePref(c, pref)
                  val _ = case ModeTable.modeLookup c'
                            of NONE => ()
                             | SOME mode => ModeTable.installMode(c, mode)
                  (* print out generated declaration *)
                  val prefix = if (! Global.printFlat) then "" else "% induced: "
                  val _ = chmsg 3 (fn () => prefix ^ (Print.conDecToString dn) ^ "\n")
               in
                  c
               end

            (* as callbackInstallConDec, but for structures *)
            fun callbackInstallStrDec(_, d : ModSyn.StrDec) =
               let
               	  val s = installStrDec(d, r)
               	  val _ = chmsg 3 (fn () => "% induced: " ^ (Print.strDecToString d) ^ "\n")
               in
               	  s
               end
            (* flatten the structure, i.e., generate all induced declarations, full type-checking of structure declaration done in this function *)
            val _ = Elab.flattenDec(c, callbackInstallConDec, callbackInstallStrDec)
                    handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
            val _ = case NewStrDec
	       of ModSyn.StrDec(_,_,dom,_, ModSyn.OpenDec opens, _) => installOpen(dom, opens, c, r)
	        | ModSyn.StrDef _ => ()
	         val _ = Comments.install c
         in
            ()
         end
      | install1 (fileName, declr as (Parser.SymInst inst, r)) = (
           let
               val (dom, cod) = case ModSyn.modLookup (ModSyn.currentMod())
                            of ModSyn.ViewDec(_, _, d, c, _) => (d,c)
                             | _  => raise ModSyn.Error(Paths.wrap(r, "instantiations only allowed in view"))
               val Inst = ReconModule.syminstToSymInst (dom, cod, inst, Paths.Loc(fileName,r))
                          handle ReconModule.Error(msg) => raise ReconModule.Error(msg) (* might also raise ReconTerm.Error or Constraints.Error *)
                               | Names.MissingModule(ns,m,s) => raise GetModule(ns,m,s)
               val NewInst = Elab.checkSymInst(Inst)
                       handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
               val c = ModSyn.instAddC(NewInst)
                       handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg))
	            val _ = Comments.install c
               val _ = chmsg 3 (fn () => Print.instToString(NewInst) ^ "\n")
	       val _ = case NewInst
	           of ModSyn.ConInst _ => ()
	            | ModSyn.StrInst _ =>
	                let
	                   fun callbackInstallInst(inst) =
	                      let
	                      	 (* @FR: add double-checking here *)
	                         val c = ModSyn.instAddC(inst)
	                                 handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg))
                                 val prefix = if (! Global.printFlat) then "" else "% induced: "
                                 val _ = if !Global.chatter >= 3
                                         then msg (prefix ^ Print.instToString(inst) ^ "\n")
		                         else ()
		               in
		               	  c
                               end
	                 in
	                    Elab.flattenInst(c, callbackInstallInst)
	                    handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
	                 end
	            | ModSyn.InclInst _ => ()
           in
             ()
           end
        )
      | install1 (fileName, declr as (Parser.SymCase cas, r)) = (
           let
               val (dom, cod) = case ModSyn.modLookup (ModSyn.currentMod())
                            of ModSyn.RelDec(_, _, d, c, _) => (d,c)
                             | _ => raise ModSyn.Error(Paths.wrap(r, "cases for logical relations only allowed in logical relation"))
               val Cas = ReconModule.symcaseToSymCase (dom, cod, cas, Paths.Loc(fileName,r))
                          handle ReconModule.Error(msg) => raise ReconModule.Error(msg) (* might also raise ReconTerm.Error or Constraints.Error *)
                               | Names.MissingModule args => raise GetModule args
               val NewCas = Elab.checkSymCase(Cas)
                       handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
               val c = ModSyn.caseAddC(NewCas)
                       handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg))
	            val _ = Comments.install c
               val _ = chmsg 3 (fn () => Print.caseToString(NewCas) ^ "\n")
	       val _ = case NewCas
	           of ModSyn.ConCase _ => ()
	            | ModSyn.StrCase _ =>
	                let
	                   fun callbackInstallCas(cas) =
	                      let
	                      	 (* @FR: add double-checking here *)
	                         val c = ModSyn.caseAddC(cas)
	                                 handle ModSyn.Error msg => raise ModSyn.Error(Paths.wrap(r, msg))
                                 val prefix = if (! Global.printFlat) then "" else "% induced: "
                                 val _ = if !Global.chatter >= 3
                                         then msg (prefix ^ Print.caseToString(cas) ^ "\n")
		                         else ()
		               in
		               	  c
                               end
	                 in
	                    Elab.flattenCase(c, callbackInstallCas)
	                    handle Elab.Error msg => raise Elab.Error(Paths.wrap(r, msg))
	                 end
	            | ModSyn.InclCase _ => ()
           in
             ()
           end
        )
      | install1 (fileName, declr as (Parser.Include incl, r)) =
         let
            val Incl as ModSyn.SigIncl(from, opendec) = ReconModule.siginclToSigIncl(incl, Paths.Loc(fileName, r))
                       handle ReconModule.Error(msg) => raise ReconModule.Error(msg)
                            | Names.MissingModule args => raise GetModule args
            val _ = Elab.checkSigIncl Incl
                       handle Elab.Error(msg) => raise Elab.Error(Paths.wrap(r,msg))
            val c = ModSyn.inclAddC(Incl)
                       handle ModSyn.Error(msg) => raise ModSyn.Error(Paths.wrap(r,msg))
            val _ = (case opendec of ModSyn.OpenDec(opens) => installOpen(from, opens, c, r);
		               Subordinate.installInclude from (* no exception should be possible *)
		      )
		      	val _ = Comments.install c
         in
            chmsg 3 (fn () => Print.sigInclToString(Incl) ^ "\n")
         end

      | install1 (fileName, (Parser.PComment(com, r), r')) = let
         val reg = Paths.toString r
         in
           (Comments.push (com,reg))
           handle Comments.Error(msg) => raise Comments.Error(Paths.wrap(r', msg))
         end

      | install1 (fileName, declr as (Parser.Namespace nsdec, r)) =
         let val ReconModule.namespace(pOpt, ns', _) = nsdec
             val ns = URI.resolve(Names.getCurrentNS(), ns')
         in case pOpt
            of SOME p => (Names.installPrefix(p,ns)
                         handle Names.Error(msg) => raise Names.Error(Paths.wrap(r, msg))
                         )
             | NONE => (Names.setCurrentNS ns;
                        Names.setDocNS(fileName, ns);
                        Comments.installDoc fileName)
         end
      | install1 (fileName, declr as (Parser.Read read, r)) =
         (* fileName: name of current elf file, possibly relative to working directory, in OS-specific syntax *)
         let
            val Read = (ReconModule.readToRead(read, Paths.Loc(fileName, r)))
               handle ReconModule.Error(msg) => raise ReconModule.Error(msg)
            val ModSyn.ReadFile ns' = Read
            (* ns' must be Unix file name relative to current file (which is itself relative to pwd
	       result is relative to pwd again *)
	    fun resolve(base, path) = let
	      val b = OS.Path.fromString (OS.Path.getParent base)
	      val p = OS.Path.fromString (OS.Path.fromUnixPath path)
	      val r = if #isAbs p then p else
	        {vol = #vol b, isAbs = #isAbs b, arcs = (#arcs b) @ (#arcs p)}
            in OS.Path.mkCanonical (OS.Path.toString r)
	    end
            val file = resolve(fileName, ns')
          in
             case Origins.linesInfoLookup file
                   of NONE => (
                      chmsg 3 (fn () => "%read \"" ^ file ^ "\".\n");
                      Origins.installLinesInfo (fileName, Paths.getLinesInfo ());
                      if loadFile file = ABORT
                      then raise ModSyn.Error("Error in included file " ^ file)
                      else ReconTerm.resetErrors fileName; (* restore previous file name *)
                           Paths.setLinesInfo(valOf (Origins.linesInfoLookup fileName))
                   ) | SOME _ =>
                      chmsg 3 (fn () => "%read \"" ^ file ^ "\". %% already read, skipping\n")
         end

    (* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
    and loadFile (fileName) = 
	handleExceptions 0 fileName (withOpenIn fileName)
	 (fn instream =>
	  let
            val _ = ReconTerm.resetErrors fileName                             (* for error messages *)
            val _ = Names.pushContext()                                        (* new namespace context *)
	    val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) (* initialize origins -fr *)
	    val res = install (fileName, Parser.parseStream instream)
	              handle e => (Names.popContext(); raise e)
	    val _ = Names.popContext()                                         (* remove the namespace context *)
	  in
	    res
	  end)

    (* loadString (str) = status
       reads and processes declarations from str, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
    fun loadString str = handleExceptions 0 "string"
	(fn () =>
	    let val _ = ReconTerm.resetErrors "string"
	        val _ = Names.pushContextIfNone()
	    in
		install ("string", Parser.parseStream (TextIO.openString str))
	    end) ()

    fun readDecl () =
        handleExceptions 0 "stdIn"
	(fn () =>
	 let
	     val _ = ReconTerm.resetErrors "stdIn"
             val _ = Names.pushContextIfNone()
             fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	     and install' (S.Empty) = ABORT
	       | install' (S.Cons (decl, s')) =
	           (install1 ("stdIn", decl); OK)
	 in
	   install (Parser.parseStream TextIO.stdIn)
	 end) ()

    (* Interactive Query Top Level *)

    fun sLoop () = if Solve.qLoop () then OK else ABORT

    fun topLoop () = case (handleExceptions 0 "stdIn" sLoop) () (* "stdIn" as fake fileName *)
		       of ABORT => topLoop ()
			| OK => ()


    (* top () = () starts interactive query loop *)
    fun top () = topLoop ()    

    (* prints declaration of symbol *)
    fun decl(s) =
       let val (modnames, names) = IDs.parseFQName s
       in case Names.nameLookup' modnames
          of NONE => (msg (IDs.foldQName modnames ^ " has not been declared\n"); ABORT)
           | SOME c =>
                let
                  val m = ModSyn.cidToMid c
                  val (dom, inSig) = case ModSyn.modLookup m
                     of ModSyn.SigDec _ => (m, true)
                      | ModSyn.ViewDec(_,_,d,_,_) => (d, false)
                      | ModSyn.RelDec(_,_,d,_,_) => (d, false)
                in
                   case Names.nameLookup [Names.CON,Names.STRUC] (dom, names)
                     of NONE => (msg (IDs.foldQName names ^ " has not been declared\n"); ABORT)
                      | SOME c' => decl' (if inSig then c' else IDs.newcid(m, IDs.lidOf c'))
                end
        end
        handle Names.Error(s) => (msg s; ABORT)
             | Names.MissingModule(_,_,s) => (msg s; ABORT)
    and decl' (cid) = (
	  (* val fixity = Names.getFixity (cid) *)
	  (* can't get name preference right now *)
	  (* val mode = ModeTable.modeLookup (cid) *)
	  (* can't get termination declaration *)
       (case ModSyn.symLookup cid
	  of ModSyn.SymCon conDec => msg (Print.conDecToString conDec ^ "\n")
	   | ModSyn.SymStr strDec => msg (Print.strDecToString strDec ^ "\n")
	   | ModSyn.SymConInst conInst => msg (Print.instToString conInst ^ "\n")
	   | ModSyn.SymStrInst strInst => msg (Print.instToString strInst ^ "\n")
	   | ModSyn.SymConCase conCase => msg (Print.caseToString conCase ^ "\n")
	   | ModSyn.SymStrCase strCase => msg (Print.caseToString strCase ^ "\n")
       ) handle ModSyn.UndefinedCid _ => msg ("no case provided\n");
       OK
    )

    (* Support tracking file modification times for smart re-appending. *)
    structure ModFile :
    sig
      type mfile
      val create : string -> mfile
      val fileName : mfile -> string
      val editName : (string -> string) -> mfile -> mfile
      val modified : mfile -> bool
      val makeModified : mfile -> unit
      val makeUnmodified : mfile -> unit
    end
    =
    struct
      type mfile = string * Time.time option ref
                   
      fun create file = (file, ref NONE)
                   
      fun fileName (file, _) = file

      fun editName edit (file, mtime) = (edit file, mtime)

      fun modified (_, ref NONE) = true
        | modified (file, ref (SOME time)) =
          (case Time.compare (time, OS.FileSys.modTime file)
             of EQUAL => false
              | _     => true)
        
      fun makeModified (_, mtime) =
          mtime := NONE

      fun makeUnmodified (file, mtime) =
          mtime := SOME (OS.FileSys.modTime file)
    end

    (* config = ["fileName1",...,"fileName<n>"] *)
    (* Files will be read in the order given! *)
    structure Config =
    struct
      (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names (which are interpreted
         relative to pwdir) along with their modification times.
         pwdir will be the current working directory
         when a configuration is loaded, which may not be same as the
         directory in which the configuration file is located.

	 This representation allows shorter file names in chatter and
	 error messages.
      *)
      type config = string * ModFile.mfile list

      (* suffix of configuration files: "cfg" by default *)
      val suffix = ref "cfg"

      (* mkRel transforms a relative path into an absolute one
         by adding the specified prefix. If the path is already
         absolute, no prefix is added to it.
      *)
      fun mkRel (prefix, path) =
          OS.Path.mkCanonical
            (if OS.Path.isAbsolute path
             then path
             else OS.Path.concat (prefix, path))

      (* more efficient recursive version  Sat 08/26/2002 -rv *)
      fun read config =
          let
            (* appendUniq (list1, list2) appends list2 to list1, removing all
               elements of list2 which are already in list1.
            *)
            fun appendUniq (l1, l2) =
                  let
                    fun appendUniq' (x :: l2) =
                          if List.exists (fn y => x = y) l1
                          then appendUniq' l2
                          else x :: appendUniq' (l2)
                      | appendUniq' nil = List.rev l1
                  in
                    List.rev (appendUniq' (List.rev l2))
                  end
            (* isConfig (item) is true iff item has the suffix of a
               configuration file.
            *)
            fun isConfig item =
                let
                  val suffix_size = (String.size (!suffix)) + 1
                  val suffix_start = (String.size item) - suffix_size
                in
                  (suffix_start >= 0)
                  andalso
                  (String.substring (item, suffix_start, suffix_size) = ("." ^ !suffix))
                end
            (* fromUnixPath path transforms path (assumed to be in Unix form)
               to the local OS conventions.
            *)
            fun fromUnixPath path =
                let
                  val vol = OS.Path.getVolume config
                  val isAbs = String.isPrefix "/" path
                  val arcs = String.tokens (fn c => c = #"/") path
                in
                  OS.Path.toString {isAbs = isAbs, vol=vol, arcs=arcs}
                end
            fun read' (sources, configs) config =
                withOpenIn config
                  (fn instream =>
                      let
                        val {dir=configDir, file=_} = OS.Path.splitDirFile config
                        fun parseItem (sources, configs) item =
                            if isConfig item
                            then
                              if List.exists (fn config' => item = config') configs
                              then (sources, configs) (* we have already read this one *)
                              else read' (sources, item :: configs) item
                            else
                              if List.exists (fn source' => item = source') sources
                              then (sources, configs) (* we have already collected this one *)
                              else (sources @ [item], configs)
                        fun parseLine (sources, configs) line =
                            if Substring.isEmpty line (* end of file *)
                            then (sources, configs)
                            else
                              let
                                val line' = Substring.dropl Char.isSpace line
                            in
                              parseLine' (sources, configs) line'
                            end
	                and parseLine' (sources, configs) line =
                            if Substring.isEmpty line (* empty line *)
                            orelse Substring.sub (line, 0) = #"%" (* comment *)
                            then parseStream (sources, configs)
                            else
                              let
                                val line' = Substring.string
                                              (Substring.takel (not o Char.isSpace) line)
                                val item = mkRel (configDir, fromUnixPath line')
                              in
                                parseStream (parseItem (sources, configs) item)
                              end
                        and parseStream (sources, configs) =
                            let
                              val line = Compat.Substring.full (Compat.inputLine97 instream)
                            in
	                      parseLine (sources, configs) line
                            end
                      in
                        parseStream (sources, configs)
                      end)
            val pwdir = OS.FileSys.getDir ()
          in
            (pwdir, List.map ModFile.create (#1(read' (nil, [config]) config)))
          (*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *)
          end

      (* Read a config file s but omit everything that is already in config c 
         XXX: naive and inefficient implementation *)
      fun readWithout (s, c) =
	  let
	      val (d,fs) = read s
	      val (d',fs') = c
	      val fns' = map (fn m => mkRel(d', ModFile.fileName m)) fs'
	      fun redundant m =
		  let 
		      val n = mkRel(d, ModFile.fileName m) 
		  in
		      List.exists (fn n' => n = n') fns'
		  end
	  in
	      (d, List.filter (not o redundant) fs)
	  end

      fun loadAbort (mfile, OK) =
	  let
	    val file = ModFile.fileName mfile
	    (* necessary for backwards compatibility: make top level declarations in file available unqualified *)
	    val _ = Names.openNamespace (URI.makeFileURI(false, file))
	    val status = loadFile file
	  in
	    case status
	      of OK => ModFile.makeUnmodified mfile
	       | _  => ();
	    status
	  end
	| loadAbort (_, ABORT) = ABORT

      (* load (config) = Status
         resets the global signature and then reads the files in config
         in order, stopping at the first error.
      *)
      fun load (config as (pwdir, sources)) = (
         reset ();
         List.app ModFile.makeModified sources;
         append (config)
      )
      (* append (config) = Status
         reads the files in config in order, beginning at the first
         modified file, stopping at the first error.
      *)
      and append (pwdir, sources) =
          let
            fun fromFirstModified nil = nil
              | fromFirstModified (sources as x::xs) =
                if ModFile.modified x
                  then sources
                  else fromFirstModified xs

            fun mkAbsolute p =
                Compat.OS.Path.mkAbsolute {path=p, relativeTo=pwdir}

            val sources' = 
                (* allow shorter messages if safe *)
                if pwdir = OS.FileSys.getDir ()
                  then sources
                else List.map (ModFile.editName mkAbsolute) sources

            val sources'' = fromFirstModified sources'
          in
            List.foldl loadAbort OK sources''
          end

      fun define (sources) = (OS.FileSys.getDir (),
                              List.map ModFile.create sources)

    end  (* structure Config *)

    (* make (configFile)
       read and then load configuration from configFile
    *)
    fun make (fileName) = 
          Config.load (Config.read fileName)
  in

    (* re-exporting environment parameters and utilities defined elsewhere *)
    structure Print :
      sig
	val implicit : bool ref		(* false, print implicit args *)
	val printInfix : bool ref	(* false, print fully explicit form infix when possible *)
	val depth : int option ref	(* NONE, limit print depth *)
	val length : int option ref	(* NONE, limit argument length *)
	val indent : int ref		(* 3, indentation of subterms *)
	val width : int ref		(* 80, line width *)
	val noShadow : bool ref	        (* if true, don't print shadowed constants as "%const%" *)
        val sgn : unit -> unit		(* print signature *)
        val prog : unit -> unit		(* print signature as program *)
	val subord : unit -> unit       (* print subordination relation *)
	val def : unit -> unit          (* print information about definitions *)
        val domains : unit -> unit	(* print available constraint domains *)
        structure TeX :			(* print in TeX format *)
	sig
	  val sgn : unit -> unit	(* print signature *)
	  val prog : unit -> unit	(* print signature as program *)
	end
	structure OMDoc : PRINTFILE     (* print in OMDoc format *)
      end
    =
    struct
      val implicit = Print.implicit
      val printInfix = Print.printInfix
      val depth = Print.printDepth
      val length = Print.printLength
      val indent = Print.Formatter.Indent
      val width = Print.Formatter.Pagewidth
      val noShadow = Print.noShadow
      fun sgn () = Print.printSgn ()
      fun prog () = ClausePrint.printSgn ()
      fun subord () = Subordinate.show ()
      fun def () = Subordinate.showDef ()
      fun domains () = msg (CSInstaller.version)
      structure TeX =
      struct
	fun sgn () = printSgnTeX ()
	fun prog () = printProgTeX ()
      end
      structure OMDoc = PrintOMDoc
    end

    structure Trace :
    sig 
      datatype 'a Spec =			(* trace specification *)
	None				(* no tracing *)
      | Some of 'a list			(* list of clauses and families *)
      | All				(* trace all clauses and families *)

      val trace : string Spec -> unit	(* clauses and families *)
      val break : string Spec -> unit	(* clauses and families *)
      val detail : int ref		(* 0 = none, 1 = default, 2 = unify *)

      val show : unit -> unit		(* show trace, break, and detail *)
      val reset : unit -> unit		(* reset trace, break, and detail *)
    end
    = Trace

    structure Timers :
      sig
	val show : unit -> unit		(* show and reset timers *)
	val reset : unit -> unit	(* reset timers *)
	val check : unit -> unit	(* display, but not no reset *)
      end
    = Timers

    structure OS  :
      sig
	val chDir : string -> unit	(* change working directory *)
	val getDir : unit -> string	(* get working directory *)
	val exit : unit -> unit		(* exit Twelf and ML *)
      end
    =
    struct
      val chDir = OS.FileSys.chDir
      val getDir = OS.FileSys.getDir
      fun exit () = OS.Process.exit (OS.Process.success)
    end

    structure Compile :
    sig
      datatype Opt = datatype CompSyn.Opt
      val optimize : Opt ref
    end
    =
    struct
      datatype Opt = datatype CompSyn.Opt      
      val optimize = CompSyn.optimize
    end

    structure Recon :
    sig
      datatype TraceMode = datatype ReconTerm.TraceMode
      val trace : bool ref
      val traceMode : TraceMode ref
    end
    =
    struct
      datatype TraceMode = datatype ReconTerm.TraceMode
      val trace = ReconTerm.trace
      val traceMode = ReconTerm.traceMode
    end

    structure Recon :
    sig
      datatype TraceMode = datatype ReconTerm.TraceMode
      val trace : bool ref
      val traceMode : TraceMode ref
    end
    =
    struct
      datatype TraceMode = datatype ReconTerm.TraceMode
      val trace = ReconTerm.trace
      val traceMode = ReconTerm.traceMode
    end

    structure Prover :
    sig					(* F=Filling, R=Recursion, S=Splitting *)
      datatype Strategy = datatype MetaGlobal.Strategy  (* FRS or RFS *)
      val strategy : Strategy ref	(* FRS, strategy used for %prove *)
      val maxSplit : int ref		(* 2, bound on splitting  *)
      val maxRecurse : int ref		(* 10, bound on recursion *)
    end
    =
    struct
      datatype Strategy = datatype MetaGlobal.Strategy  (* FRS or RFS *)
      val strategy = MetaGlobal.strategy
      val maxSplit = MetaGlobal.maxSplit
      val maxRecurse = MetaGlobal.maxRecurse
    end

    val chatter : int ref = Global.chatter
    val doubleCheck : bool ref = Global.doubleCheck
    val unsafe : bool ref = Global.unsafe
    val autoFreeze : bool ref = Global.autoFreeze
    val timeLimit : (Time.time option) ref = Global.timeLimit
    val printFlat : bool ref = Global.printFlat (* -fr *)

    datatype Status = datatype Status
    val reset = reset
    (* reset if nothing read yet *)
    val loadFile = loadFile
    val loadString = loadString
    val readDecl = readDecl
    val decl = decl

    val top = top

    structure Config :
      sig
	type config			(* configuration *)
        val suffix : string ref         (* suffix of configuration files *)
	val read : string -> config	(* read configuration from config file *)
	val readWithout : string * config -> config 
                                        (* read config file, minus contents of another *)
	val load : config -> Status	(* reset and load configuration *)
	val append : config -> Status	(* load configuration (w/o reset) *)
	val define : string list -> config  (* explicitly define configuration *)
      end
    = Config
    val make = make

    val version = Version.version_string

    val version = "Twelf 1.6beta, June 2010 (%trustme)"
    structure Table : 
      sig 
	datatype Strategy = datatype TableParam.Strategy
	val strategy : Strategy ref
	val strengthen : bool ref
	val resetGlobalTable : unit -> unit
	val top : unit -> unit
      end 
    = 
  struct
    datatype Strategy = datatype TableParam.Strategy
    val strategy = TableParam.strategy
    val strengthen = TableParam.strengthen
      	  
    val resetGlobalTable = TableParam.resetGlobalTable

    (* top () = () starts interactive query loop *)
    fun top () = 
      let 
	fun sLoopT () = if Solve.qLoopT () then OK else ABORT
      
	fun topLoopT () = 
	  case (handleExceptions 0 "stdIn" sLoopT) () (* "stdIn" as fake fileName *)
	    of ABORT => topLoopT ()
	  | OK => ()
      in 
	topLoopT ()
      end 
  end

  end  (* local *)
end; (* functor Twelf *)
