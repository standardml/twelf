(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow *)
(* Modified: Brigitte Pientka, Roberto Virga *)

functor Twelf
  (structure Global : GLOBAL
   structure Timers : TIMERS
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'

   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Paths : PATHS
   structure Origins : ORIGINS
     sharing Origins.Paths = Paths
   structure Lexer : LEXER
     sharing Lexer.Paths = Paths
   structure Parsing : PARSING
     sharing Parsing.Lexer = Lexer
   structure Parser : PARSER
     sharing Parser.Names = Names
     sharing Parser.ExtSyn.Paths = Paths
   structure TypeCheck : TYPECHECK
   structure Strict : STRICT
     sharing Strict.IntSyn = IntSyn'
     sharing Strict.Paths = Paths
   structure Constraints : CONSTRAINTS
     sharing Constraints.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure ReconTerm : RECON_TERM
     sharing ReconTerm.IntSyn = IntSyn'
     sharing ReconTerm.Paths = Paths
     sharing type ReconTerm.term = Parser.ExtSyn.term
     (* sharing type ReconTerm.Paths.occConDec = Origins.Paths.occConDec *)
   structure ReconConDec : RECON_CONDEC
     sharing ReconConDec.IntSyn = IntSyn'
     sharing ReconConDec.Paths = Paths
     sharing type ReconConDec.condec = Parser.ExtConDec.condec
   structure ReconQuery : RECON_QUERY

   structure ModeSyn : MODESYN
     sharing ModeSyn.IntSyn = IntSyn'
   structure ModeCheck : MODECHECK
     sharing ModeCheck.IntSyn = IntSyn'
     sharing ModeCheck.ModeSyn = ModeSyn
     sharing ModeCheck.Paths = Paths
   structure ReconMode : RECON_MODE
     sharing ReconMode.ModeSyn = ModeSyn
     sharing ReconMode.Paths = Paths
     sharing type ReconMode.modedec = Parser.ExtModes.modedec
   structure ModePrint : MODEPRINT
     sharing ModePrint.ModeSyn = ModeSyn
   structure ModeDec : MODEDEC
     sharing ModeDec.ModeSyn = ModeSyn
     sharing ModeDec.Paths = Paths

   structure Cover : COVER
     sharing Cover.IntSyn = IntSyn'
     sharing Cover.ModeSyn = ModeSyn

   structure Total : TOTAL
     sharing Total.IntSyn = IntSyn'

   structure Reduces : REDUCES
     sharing Reduces.IntSyn = IntSyn'

   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure IndexSkolem : INDEX
     sharing IndexSkolem.IntSyn = IntSyn'
   structure Subordinate : SUBORDINATE
     sharing Subordinate.IntSyn = IntSyn'
   structure CompSyn' : COMPSYN
     sharing CompSyn'.IntSyn = IntSyn'
   structure Compile : COMPILE
     sharing Compile.IntSyn = IntSyn'
     sharing Compile.CompSyn = CompSyn'
   structure AbsMachine : ABSMACHINE
     sharing AbsMachine.IntSyn = IntSyn'
     sharing AbsMachine.CompSyn = CompSyn'

   structure Tabled : TABLED
     sharing Tabled.IntSyn = IntSyn'
     sharing Tabled.CompSyn = CompSyn'
   structure TableIndex : TABLEINDEX
     sharing TableIndex.IntSyn = IntSyn'
   structure Solve : SOLVE
     sharing Solve.IntSyn = IntSyn'
     sharing type Solve.ExtQuery.query = Parser.ExtQuery.query
     sharing type Solve.ExtQuery.define = Parser.ExtQuery.define
     sharing type Solve.ExtQuery.solve = Parser.ExtQuery.solve
     sharing Solve.Paths = Paths

   structure ThmSyn : THMSYN
     sharing ThmSyn.Paths = Paths
     sharing ThmSyn.Names = Names
   structure Thm : THM
     sharing Thm.ThmSyn = ThmSyn
     sharing Thm.Paths = Paths
   structure ReconThm : RECON_THM
     sharing ReconThm.ThmSyn = ThmSyn
     sharing ReconThm.Paths = Paths
     sharing ReconThm.ThmSyn.ModeSyn = ModeSyn
     sharing type ReconThm.tdecl = Parser.ThmExtSyn.tdecl
     sharing type ReconThm.rdecl = Parser.ThmExtSyn.rdecl (* -bp *)
     sharing type ReconThm.tableddecl = Parser.ThmExtSyn.tableddecl (* -bp *)
     sharing type ReconThm.wdecl = Parser.ThmExtSyn.wdecl 
     sharing type ReconThm.theorem = Parser.ThmExtSyn.theorem
     sharing type ReconThm.theoremdec = Parser.ThmExtSyn.theoremdec 
     sharing type ReconThm.prove = Parser.ThmExtSyn.prove
     sharing type ReconThm.establish = Parser.ThmExtSyn.establish
     sharing type ReconThm.assert = Parser.ThmExtSyn.assert
   structure ThmPrint : THMPRINT
     sharing ThmPrint.ThmSyn = ThmSyn

   structure TabledSyn : TABLEDSYN
     sharing TabledSyn.IntSyn = IntSyn'

   structure WorldSyn : WORLDSYN
     sharing WorldSyn.IntSyn = IntSyn'
   structure WorldPrint : WORLDPRINT
     sharing WorldPrint.WorldSyn = WorldSyn

   structure ModSyn : MODSYN
     sharing ModSyn.IntSyn = IntSyn'
     sharing ModSyn.Names = Names
     sharing ModSyn.Paths = Paths
   structure ReconModule : RECON_MODULE
     sharing ReconModule.ModSyn = ModSyn
     sharing type ReconModule.sigdef = Parser.ModExtSyn.sigdef
     sharing type ReconModule.structdec = Parser.ModExtSyn.structdec
     sharing type ReconModule.sigexp = Parser.ModExtSyn.sigexp
     sharing type ReconModule.strexp = Parser.ModExtSyn.strexp

   structure MetaGlobal : METAGLOBAL
   structure FunSyn : FUNSYN
     sharing FunSyn.IntSyn = IntSyn'
   structure Skolem : SKOLEM
     sharing Skolem.IntSyn = IntSyn'
   structure Prover : PROVER
     sharing Prover.IntSyn = IntSyn'
   structure ClausePrint : CLAUSEPRINT
     sharing ClausePrint.IntSyn = IntSyn'

   structure Trace : TRACE

   structure PrintTeX : PRINT
     sharing PrintTeX.IntSyn = IntSyn'
   structure ClausePrintTeX : CLAUSEPRINT
     sharing ClausePrintTeX.IntSyn = IntSyn'

   structure CSManager : CS_MANAGER
     sharing CSManager.IntSyn = IntSyn'
     sharing CSManager.Fixity = Names.Fixity
     sharing CSManager.ModeSyn = ModeSyn)
 :> TWELF =
struct

  local
    structure IntSyn = IntSyn'
    structure S = Parser.Stream

    fun fileOpenMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => print ("[Loading file " ^ fileName ^ " ...")
	    | _ => print ("[Opening file " ^ fileName ^ "]\n"))

    fun fileCloseMsg (fileName) =
	(case !Global.chatter
	   of 0 => ()
	    | 1 => print ("]\n")
	    | _ => print ("[Closing file " ^ fileName ^ "]\n"))

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
        (print "\\begin{bigcode}\n";
	 ClausePrintTeX.printSgn ();
	 print "\\end{bigcode}\n")

    fun printSgnTeX () =
        (print "\\begin{bigcode}\n";
	 PrintTeX.printSgn ();
         print "\\end{bigcode}\n")

    (* status ::= OK | ABORT  is the return status of various operations *)
    datatype Status = OK | ABORT

    fun abort (msg) = (print (msg); ABORT)
    fun abortFileMsg (fileName, msg) = abort (fileName ^ ":" ^ msg ^ "\n")

    fun abortIO (fileName, {cause = OS.SysErr (msg, _), function = f, name = n}) =
	(print ("IO Error on file " ^ fileName ^ ":\n" ^ msg ^ "\n");
	 ABORT)
      | abortIO (fileName, {function = f, ...}) =
	(print ("IO Error on file " ^ fileName ^ " from function "
		       ^ f ^ "\n");
	 ABORT)


    (* should move to paths, or into the prover module... but not here! -cs *)
    fun joinregion (r, nil) = r
      | joinregion (r, r' :: rs) = 
          joinregion (Paths.join (r, r'), rs)

    fun joinregions (r::rs) = joinregion (r, rs)

    fun constraintsMsg (cnstrL) =
        "Typing ambiguous -- unresolved constraints\n" ^ Print.cnstrsToString cnstrL

    (* val handleExceptions : string -> ('a -> Status) -> 'a -> Status *)
    (* handleExceptions filename f x = f x
       where standard exceptions are handled and an appropriate error message is
       issued.  Unrecognized exceptions are re-raised.
    *)
    fun handleExceptions fileName (f:'a -> Status) (x:'a) =
	(f x
	 handle ReconTerm.Error (msg) => abortFileMsg (fileName, msg)
	      | ReconConDec.Error (msg) => abortFileMsg (fileName, msg)
	      | ReconQuery.Error (msg) => abortFileMsg (fileName, msg)
	      | ReconMode.Error (msg) => abortFileMsg (fileName, msg)
	      | ReconThm.Error (msg) => abortFileMsg (fileName, msg)
              | ReconModule.Error (msg) => abortFileMsg (fileName, msg)
	      | TypeCheck.Error (msg) => abort ("Double-checking types fails: " ^ msg ^ "\n"
						^ "This indicates a bug in Twelf.\n")
	      | Abstract.Error (msg) => abortFileMsg (fileName, msg)
	      (* | Constraints.Error (cnstrL) => abortFileMsg (fileName, constraintsMsg cnstrL) *)
	      | Total.Error (msg) => abort (msg ^ "\n")	(* Total includes filename *)
	      | Reduces.Error (msg) => abort (msg ^ "\n") (* Reduces includes filename *)
              | Compile.Error (msg) => abortFileMsg (fileName, msg)
	      | Thm.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeSyn.Error (msg) => abortFileMsg (fileName, msg)
	      | ModeCheck.Error (msg) => abort (msg ^ "\n") (* ModeCheck includes filename *)
	      | ModeDec.Error (msg) => abortFileMsg (fileName, msg)
              | Cover.Error (msg) => abortFileMsg (fileName, msg)
	      | Parsing.Error (msg) => abortFileMsg (fileName, msg)
	      | Lexer.Error (msg) => abortFileMsg (fileName, msg)
	      | IntSyn.Error (msg) => abort ("Signature error: " ^ msg ^ "\n")
	      | Names.Error (msg) => abortFileMsg (fileName, msg)
	      | IO.Io (ioError) => abortIO (fileName, ioError)
	      | Solve.AbortQuery (msg) => abortFileMsg (fileName, msg)
	      | ThmSyn.Error (msg) => abortFileMsg (fileName, msg)
	      | Prover.Error (msg) => abortFileMsg (fileName, msg)
	      | Strict.Error (msg) => abortFileMsg (fileName, msg)
              | Subordinate.Error (msg) => abortFileMsg (fileName, msg)
	      | WorldSyn.Error (msg) => abort (msg ^ "\n") (* includes filename *)
              | ModSyn.Error (msg) => abortFileMsg (fileName, msg)
              | CSManager.Error (msg) => abort ("Constraint Solver Manager error: " ^ msg ^ "\n")
	      | exn => (abort ("Unrecognized exception\n"); raise exn))

    (* During elaboration of a signature expression, each constant
       that that the user declares is added to this table.  At top level,
       however, the reference holds NONE (in particular, shadowing is
       allowed).
    *)
    val context : Names.namespace option ref = ref NONE

    fun installConst fromCS (cid, fileNameocOpt) =
        let
          val _ = Origins.installOrigin (cid, fileNameocOpt)
          val _ = Index.install fromCS (IntSyn.Const cid)
          val _ = IndexSkolem.install fromCS (IntSyn.Const cid)
          val _ = (Timers.time Timers.compiling Compile.install) fromCS cid
          val _ = (Timers.time Timers.subordinate Subordinate.install) cid
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
	  val cid = IntSyn.sgnAdd conDec
	  val _ = (case (fromCS, !context)
		     of (IntSyn.Ordinary, SOME namespace) => Names.insertConst (namespace, cid)
		      | (IntSyn.Clause, SOME namespace) => Names.insertConst (namespace, cid)
		      | _ => ())
	          handle Names.Error msg =>
		    raise Names.Error (Paths.wrap (r, msg))
	  val _ = Names.installConstName cid
	  val _ = installConst fromCS (cid, fileNameocOpt)
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end

    fun installBlockDec fromCS (conDec, fileNameocOpt as (fileName, ocOpt), r) =
	let
	  val cid = IntSyn.sgnAdd conDec
	  val _ = (case (fromCS, !context)
		     of (IntSyn.Ordinary, SOME namespace) => Names.insertConst (namespace, cid)
		        (* (Clause, _) should be impossible *)
		      | _ => ())
	           handle Names.Error msg =>
		     raise Names.Error (Paths.wrap (r, msg))
	  val _ = Names.installConstName cid
	  val _ = Origins.installLinesInfo (fileName, Paths.getLinesInfo ())
	in 
	  cid
	end


    fun installStrDec (strdec, module, r, isDef) =
        let
          fun installAction (data as (cid, _)) =
              (installConst IntSyn.Ordinary data;
	       if !Global.chatter >= 4
                 then print (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
               else ())


          val _ = ModSyn.installStruct (strdec, module, !context,
                                        installAction, isDef)
                  handle Names.Error msg =>
                           raise Names.Error (Paths.wrap (r, msg))
        in
          ()
        end

    fun includeSig (module, r, isDef) =
        let
          fun installAction (data as (cid, _)) =
              (installConst IntSyn.Ordinary data;
	       if !Global.chatter >= 4
                 then print (Print.conDecToString (IntSyn.sgnLookup cid) ^ "\n")
               else ())

          val _ = ModSyn.installSig (module, !context,
                                     installAction, isDef)
                  handle Names.Error msg =>
                           raise Names.Error (Paths.wrap (r, msg))
        in
          ()
        end

    (* install1 (decl) = ()
       Installs one declaration
       Effects: global state
                may raise standard exceptions
    *)
    fun install1 (fileName, (Parser.ConDec condec, r)) =
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
	(* Clauses %clause c = u or %clause c : V = U or %clause c : V *)
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
      (* %queryTabled <expected> <try> A or %query <expected> <try> X : A *)
      | install1 (fileName, (Parser.Querytabled(numSol, try,query), r)) =
        (* Solve.query might raise Solve.AbortQuery (msg) *)
	(Solve.querytabled ((numSol, try, query), Paths.Loc (fileName, r))
	 handle Solve.AbortQuery (msg)
	        => raise Solve.AbortQuery (Paths.wrap (r, msg)))

      (* %freeze <qid> ... *)
      | install1 (fileName, (Parser.FreezeDec (qids), r)) = 
        let
          fun toCid qid =
              case Names.constLookup qid
                of NONE => raise Names.Error ("Undeclared identifier "
                                              ^ Names.qidToString (valOf (Names.constUndef qid))
                                              ^ " in freeze assertion")
                 | SOME cid => cid
          val cids = List.map toCid qids
                     handle Names.Error (msg) => raise Names.Error (Paths.wrap (r, msg))
        in
          Subordinate.installFrozen cids
          handle Subordinate.Error (msg) => raise Subordinate.Error (Paths.wrap (r, msg));
          if !Global.chatter >= 3
          then print ((if !Global.chatter >= 4 then "%" else "")
                      ^ "%freeze"
                      ^ List.foldr (fn (a, s) => " " ^ Names.qidToString (Names.constQid a) ^ s) ".\n" cids)
          else ()
        end

      (* %deterministic <qid> ... *)
      | install1 (fileName, (Parser.DeterministicDec (qids), r)) = 
        let
          fun toCid qid =
              case Names.constLookup qid
                of NONE =>
                    raise Names.Error ("Undeclared identifier "
                                       ^ Names.qidToString (valOf (Names.constUndef qid))
                                       ^ " in deterministic declaration")
                 | SOME cid => cid
          fun insertCid cid = CompSyn.detTableInsert (cid, true)
          val cids = List.map toCid qids
                       handle Names.Error (msg) =>
                         raise Names.Error (Paths.wrap (r, msg))
        in
          List.map insertCid cids;
          if !Global.chatter >= 3
          then print ((if !Global.chatter >= 4 then "%" else "")
                      ^ "%deterministic"
                      ^ List.foldr (fn (a, s) => " " ^ Names.qidToString (Names.constQid a) ^ s) ".\n" cids)
          else ()
        end

      (* Fixity declaration for operator precedence parsing *)
      | install1 (fileName, (Parser.FixDec ((qid,r),fixity), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in fixity declaration")
            | SOME cid => (Names.installFixity (cid, fixity);
                           if !Global.chatter >= 3
                             then print ((if !Global.chatter >= 4 then "%" else "")
                                         ^ Names.Fixity.toString fixity ^ " "
                                         ^ Names.qidToString (Names.constQid cid) ^ ".\n")
                           else ())
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Name preference declaration for printing *)
      | install1 (fileName, (Parser.NamePref ((qid,r), namePref), _)) =
        (case Names.constLookup qid
           of NONE => raise Names.Error ("Undeclared identifier "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ " in name preference")
            | SOME cid => Names.installNamePref (cid, namePref)
	 handle Names.Error (msg) => raise Names.Error (Paths.wrap (r,msg)))

      (* Mode declaration *)
      | install1 (fileName, (Parser.ModeDec mterms, r)) =
	let 
	  val mdecs = List.map ReconMode.modeToMode mterms
          val _ = ReconTerm.checkErrors (r)
	  val _ = List.app (fn (mdec as (a, _), r) => 
	                    (case (IntSyn.conDecStatus (IntSyn.sgnLookup a))
			       of IntSyn.Normal => ModeSyn.installMode mdec
			        | _ => raise ModeSyn.Error "Cannot declare modes for foreign constants")
			    handle ModeSyn.Error (msg) => raise ModeSyn.Error (Paths.wrap (r, msg)))
	          mdecs
	  val _ = List.app (fn (mdec, r) => ModeCheck.checkMode mdec (* exception comes with location *)
			    handle ModeCheck.Error (msg) => raise ModeCheck.Error (msg))
	          mdecs
	  val _ = if !Global.chatter >= 3 
		    then print ("%mode " ^ ModePrint.modesToString
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
	  val _ = List.app (fn (mdec, r) => Cover.checkCovers mdec
			    handle Cover.Error (msg) => raise Cover.Error (Paths.wrap (r, msg)))
	          mdecs
	  val _ = if !Global.chatter >= 3
		    then print ("%covers " ^ ModePrint.modesToString
				             (List.map (fn (mdec, r) => mdec) mdecs)
					   ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Total declaration *)
      | install1 (fileName, (Parser.TotalDec lterm, r)) =
	let
	  val _ = if not (!Global.unsafe)
		    then raise Total.Error (Paths.wrapLoc (Paths.Loc (fileName, r), "%total not safe: Toggle `unsafe' flag"))
	          else ()

	  val (T, rrs as (r,rs)) = ReconThm.tdeclTotDecl lterm
	  val La = Thm.installTotal (T, rrs)
	  val _ = map Total.install La	(* pre-install for recursive checking *)
	  val _ = map Total.checkFam La
	          handle Total.Error (msg) => raise Total.Error (msg) (* include region and file *)
		       | Cover.Error (msg) => raise Cover.Error (Paths.wrap (r, msg))
		       | Reduces.Error (msg) => raise Reduces.Error (msg) (* includes filename *)
	  val _ = if !Global.chatter >= 3
		    then print ("%total " ^ ThmPrint.tDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

      (* Termination declaration *)
      | install1 (fileName, (Parser.TerminatesDec lterm, _)) =
	let
	  val (T, rrs) = ReconThm.tdeclTotDecl lterm 
	  val La = Thm.installTerminates (T, rrs)
  	  val _ = map (Timers.time Timers.terminate Reduces.checkFam) La   
	  val _ = if !Global.chatter >= 3 
		    then print ("%terminates " ^ ThmPrint.tDeclToString T ^ ".\n")
		  else ()
	in
	  ()
	end

        (* -bp *)
	(* Reduces declaration *)
      | install1 (fileName, (Parser.ReducesDec lterm, _)) =
	let
	  val (R, rrs) = ReconThm.rdeclTorDecl lterm 
	  val La = Thm.installReduces (R, rrs)
	  (*  -bp6/12/99.   *)
	  val _ = map (Timers.time Timers.terminate Reduces.checkFamReduction) La
	  val _ = if !Global.chatter >= 3 
		    then print ("%reduces " ^ ThmPrint.rDeclToString R ^ ".\n")
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
		    then print ("%tabled " ^ ThmPrint.tabledDeclToString T ^ ".\n")
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
	  val _ = ModeSyn.installMode (cid, MS)
	  val _ = if !Global.chatter >= 3
		    then print ("%theorem " ^ Print.conDecToString E ^ "\n")
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
		    then print ("%prove " ^ (Int.toString depth) ^ " " ^
				       (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	  val _ = Prover.init (depth, La)
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => print ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeSyn.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]

	  val _ = Prover.auto ()
	          handle Prover.Error msg
		         => raise Prover.Error (Paths.wrap (joinregion rrs, msg)) (* times itself *)
	  val _ = if !Global.chatter >= 3 
		    then print ("%QED\n")
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
		    then print ("%prove " ^ (Int.toString depth) ^ " " ^
				       (ThmPrint.tDeclToString T) ^ ".\n")
		  else ()
	  val _ = Prover.init (depth, La)
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => print ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeSyn.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]

	  val _ = Prover.auto () handle Prover.Error msg => raise Prover.Error (Paths.wrap (joinregion rrs, msg)) (* times itself *)
		    
	in
	  Prover.install (fn E => installConDec IntSyn.Ordinary (E, (fileName, NONE), r))
	end 

      (* Establish declaration *)
      | install1 (fileName, (Parser.AssertDec aterm, _)) =
	let 
	  val _ = if not (!Global.unsafe)
		    then raise ThmSyn.Error "%assert not safe: Toggle `unsafe' flag"
	          else ()
	  val (cp as ThmSyn.Callpats (L), rrs) = ReconThm.assertToAssert aterm 
	  val La = map (fn (c, P) => c) L  (* La is the list of type constants *)
	  val _ = if !Global.chatter >= 3 
		    then print ("%assert " ^ (ThmPrint.callpatsToString cp) ^ ".\n")
		  else ()
	  val _ = if !Global.chatter >= 3 
		    then map (fn a => print ("%mode " ^ 
					     (ModePrint.modeToString (a, valOf (ModeSyn.modeLookup a)))
					     ^ ".\n")) La   (* mode must be declared!*)
		  else [()]
	in
	  Skolem.install La
	end
      | install1 (fileName, (Parser.WorldDec wdecl, _)) =
	let
	  val (ThmSyn.WDecl (qids, cp as ThmSyn.Callpats cpa), rs) =
	         ReconThm.wdeclTowDecl wdecl
	  val W = WorldSyn.Worlds
	      (List.map (fn qid => case Names.constLookup qid
			            of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid)
	      qids)
	  val _ = List.app (fn (a, _) => WorldSyn.install (a, W)) cpa
	          handle WorldSyn.Error (msg)
		         (* error location inaccurate here *)
		         => raise WorldSyn.Error (Paths.wrapLoc (Paths.Loc (fileName, joinregions rs), msg))
	  val _ = if !Global.chatter >= 3 
		    then print ("%worlds " ^ WorldPrint.worldsToString W ^ " "
				^ ThmPrint.callpatsToString cp ^ ".\n")
		  else ()
	in
	  (map (fn (a, _) => WorldSyn.worldcheck W a) cpa ; ())
	end
      | install1 (fileName, declr as (Parser.SigDef _, _)) =
          install1WithSig (fileName, NONE, declr)
      | install1 (fileName, declr as (Parser.StructDec _, _)) =
          install1WithSig (fileName, NONE, declr)
      | install1 (fileName, declr as (Parser.Include _, _)) =
          install1WithSig (fileName, NONE, declr)
      | install1 (fileName, declr as (Parser.Open _, _)) =
          install1WithSig (fileName, NONE, declr)
      | install1 (fileName, (Parser.Use name, r)) =
        (case !context
           of NONE => CSManager.useSolver (name)
            | _ => raise ModSyn.Error (Paths.wrap (r, "%use declaration needs to be at top level")))

    and install1WithSig (fileName, moduleOpt, (Parser.SigDef sigdef, r)) =
        (* Signature declaration *)
        let
          (* FIX: should probably time this -kw *)
          val (idOpt, module, wherecls) =
                ReconModule.sigdefToSigdef (sigdef, moduleOpt)
          val module' = foldl (fn (inst, module) => ReconModule.moduleWhere (module, inst)) module wherecls
          val name = (case idOpt
                        of SOME id => (ModSyn.installSigDef (id, module');
                                       id)
                         | NONE => "_" (* anonymous *))
                  handle ModSyn.Error msg => raise ModSyn.Error (Paths.wrap (r, msg))
	  val _ = if !Global.chatter >= 3 
		    then print ("%sig " ^ name ^ " = { ... }.\n")
		  else ()
        in
          ()
        end
      | install1WithSig (fileName, moduleOpt, (Parser.StructDec structdec, r)) =
        (* Structure declaration *)
        (case ReconModule.structdecToStructDec (structdec, moduleOpt)
           of ReconModule.StructDec (idOpt, module, wherecls) =>
              let
                val module' = foldl (fn (inst, module) => ReconModule.moduleWhere (module, inst)) module wherecls
                val name = (case idOpt
                              of SOME id =>
                                   (installStrDec (IntSyn.StrDec (id, NONE), module', r, false);
                                    id)
                               | NONE => "_" (* anonymous *))
                val _ = if !Global.chatter = 3
                          then print ("%struct " ^ name ^ " : { ... }.\n")
                        else ()
              in
                ()
              end
            | ReconModule.StructDef (idOpt, mid) =>
              let
                val ns = Names.getComponents mid
                val module = ModSyn.abstractModule (ns, SOME mid)
                val name = (case idOpt
                              of SOME id =>
                                   (installStrDec (IntSyn.StrDec (id, NONE), module, r, true);
                                    id)
                               | NONE => "_" (* anonymous *))
                val _ = if !Global.chatter = 3
                          then print ("%struct " ^ name ^ " = " ^ Names.qidToString (Names.structQid mid) ^ ".\n")
                        else ()
              in
                ()
              end)
          
      | install1WithSig (fileName, moduleOpt, (Parser.Include sigexp, r)) =
        (* Include declaration *)
        let
          val (module, wherecls) = ReconModule.sigexpToSigexp (sigexp, moduleOpt)
          val module' = foldl (fn (inst, module) => ReconModule.moduleWhere (module, inst)) module wherecls
          val _ = includeSig (module', r, false)
          val _ = if !Global.chatter = 3
                    then print ("%include { ... }.\n")
                  else ()
        in
          ()
        end

      | install1WithSig (fileName, NONE, (Parser.Open strexp, r)) =
        (* Open declaration *)
        let
          val mid = ReconModule.strexpToStrexp strexp
          val ns = Names.getComponents mid
          val module = ModSyn.abstractModule (ns, SOME mid)
          val _ = includeSig (module, r, true)
          val _ = if !Global.chatter = 3
                    then print ("%open " ^ Names.qidToString (Names.structQid mid) ^ ".\n")
                  else ()
        in
          ()
        end

    fun installSubsig (fileName, s) =
        let
          val namespace = Names.newNamespace ()

          val (mark, markStruct) = IntSyn.sgnSize ()
          val markSigDef = ModSyn.sigDefSize ()
          val oldContext = !context
          val _ = context := SOME namespace
          val _ = if !Global.chatter >= 4
                    then print ("\n% begin subsignature\n")
                  else ()

          fun install s = install' ((Timers.time Timers.parsing S.expose) s)
          and install' (S.Cons ((Parser.BeginSubsig, _), s')) =
                install (installSubsig (fileName, s'))
            | install' (S.Cons ((Parser.EndSubsig, _), s')) = s'
            | install' (S.Cons (declr, s')) =
                (install1 (fileName, declr); install s')

          val result =
              let
                val s' = install s
                val module = ModSyn.abstractModule (namespace, NONE)
                val _ = if !Global.chatter >= 4
                          then print ("% end subsignature\n\n")
                        else ()
              in
                Value (module, s')
              end
              handle exn => Exception exn

          val _ = context := oldContext

          val _ = Names.resetFrom (mark, markStruct)
          val _ = Index.resetFrom mark
          val _ = IndexSkolem.resetFrom mark
          val _ = ModSyn.resetFrom markSigDef
          (* val _ = ModeSyn.resetFrom mark *)
          (* val _ = Total.resetFrom mark *)
          (* val _ = Subordinate.resetFrom mark (* ouch! *) *)
          (* val _ = Reduces.resetFrom mark *)
          (* Origins, CompSyn, FunSyn harmless? -kw *)
          (* val _ = IntSyn.resetFrom (mark, markStruct)
             FIX: DON'T eliminate out-of-scope cids for now -kw *)
        in
          case result
            of Value (module, s') =>
               let
                 val S.Cons (declr, s'') =
                       (Timers.time Timers.parsing S.expose) s'
               in
                 install1WithSig (fileName, SOME module, declr);
                 s''
               end
             | Exception exn => raise exn
        end

    (* loadFile (fileName) = status
       reads and processes declarations from fileName in order, issuing
       error messages and finally returning the status (either OK or
       ABORT).
    *)
    fun loadFile (fileName) = 
	handleExceptions fileName (withOpenIn fileName)
	 (fn instream =>
	  let
            val _ = ReconTerm.resetErrors fileName
	    fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	    and install' (S.Empty) = OK
	        (* Origins.installLinesInfo (fileName, Paths.getLinesInfo ()) *)
	        (* now done in installConDec *)
              | install' (S.Cons((Parser.BeginSubsig, _), s')) =
                  install (installSubsig (fileName, s'))
	      | install' (S.Cons(decl, s')) =
	        (install1 (fileName, decl); install s')
	  in
	    install (Parser.parseStream instream)
	  end)

    (* Interactive Query Top Level *)

    fun sLoop () = if Solve.qLoop () then OK else ABORT

    fun topLoop () = case (handleExceptions "stdIn" sLoop) () (* "stdIn" as fake fileName *)
		       of ABORT => topLoop ()
			| OK => ()


    (* top () = () starts interactive query loop *)
    fun top () = topLoop ()    

    fun installCSMDec (conDec, optFixity, optMdec) = 
	let
	  val _ = ModeCheck.checkD (conDec, "%use", NONE)
          (* put a more reasonable region here? -kw *)
	  val cid = installConDec IntSyn.FromCS (conDec, ("", NONE), Paths.Reg (0,0))
	  val _ = if !Global.chatter >= 3
		  then print (Print.conDecToString (conDec) ^ "\n")
		  else ()
	  val _ = (case optFixity
		     of SOME(fixity) =>
			  (Names.installFixity (cid, fixity);
                           if !Global.chatter >= 3
                             then print ((if !Global.chatter >= 4 then "%" else "")
                                         ^ Names.Fixity.toString fixity ^ " "
                                         ^ Names.qidToString (Names.constQid cid) ^ ".\n")
                           else ())
		      | NONE => ())
	  val _ = (case optMdec
		     of SOME(mdec) =>
			  ModeSyn.installMode (cid, mdec)
		      | NONE => ())
	in
	  cid
	end

    val _ = CSManager.setInstallFN (installCSMDec)
 
    (* reset () = () clears all global tables, including the signature *)
    fun reset () = (IntSyn.sgnReset (); Names.reset (); Origins.reset ();
		    ModeSyn.reset ();
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
                    ModSyn.reset ();
                    CSManager.resetSolvers ();
                    context := NONE
		    )

    fun readDecl () =
        handleExceptions "stdIn"
	(fn () =>
	 let val _ = ReconTerm.resetErrors "stdIn"
             fun install s = install' ((Timers.time Timers.parsing S.expose) s)
	     and install' (S.Empty) = ABORT
               | install' (S.Cons((Parser.BeginSubsig, _), s')) =
                   (installSubsig ("stdIn", s'); OK)
	       | install' (S.Cons (decl, s')) =
	           (install1 ("stdIn", decl); OK)
	 in
	   install (Parser.parseStream TextIO.stdIn)
	 end) ()

    (* decl (id) = () prints declaration of constant id *)
    fun decl (id) =
        (case Names.stringToQid id
           of NONE => (print (id ^ " is not a well-formed qualified identifier\n"); ABORT)
            | SOME qid => 
        (case Names.constLookup qid
           of NONE => (print (Names.qidToString (valOf (Names.constUndef qid)) ^ " has not been declared\n"); ABORT)
            | SOME cid => decl' (cid)))
    and decl' (cid) =
        let
	  val conDec = IntSyn.sgnLookup (cid)
	  (* val fixity = Names.getFixity (cid) *)
	  (* can't get name preference right now *)
	  (* val mode = ModeSyn.modeLookup (cid) *)
	  (* can't get termination declaration *)
	in
	  print (Print.conDecToString conDec ^ "\n");
	  OK
	end

    (* config = ["fileName1",...,"fileName<n>"] *)
    (* Files will be read in the order given! *)
    structure Config =
    struct
      (* A configuration (pwdir, sources) consists of an absolute directory
         pwdir and a list of source file names which are interpreted
         relative to pwdir.  pwdir will be the current working directory
         when a configuration is loaded, which may not be same as the
         directory in which the configuration file is located.

	 This representation allows shorter file names in chatter and
	 error messages.
      *)
      type config = string * string list

      (* suffix of configuration files: "cfg" by default *)
      val suffix = ref "cfg"

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
	    (* mkRel transforms a relative path into an absolute one
               by adding the specified prefix. If the path is already
               absolute, no prefix is added to it.
            *)
	    fun mkRel (prefix, path) =
                OS.Path.mkCanonical
                  (if OS.Path.isAbsolute path
                   then path
                   else OS.Path.concat (prefix, path))
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
                              val line = Substring.all (TextIO.inputLine instream)
                            in
	                      parseLine (sources, configs) line
                            end
                      in
                        parseStream (sources, configs)
                      end)
            val pwdir = OS.FileSys.getDir ()
          in
            (pwdir, #1(read' (nil, [config]) config))
          (*
            handle IO.Io (ioError) => (abortIO (configFile, ioError); raise IO.io (ioError))
          *)
          end

      fun loadAbort (filename, OK) = loadFile (filename)
	| loadAbort (_, ABORT) = ABORT

      (* load (config) = Status
         resets the global signature and then reads the files in config
         in order, stopping at the first error.
      *)
      fun load (config) =
          (reset (); append (config))
      (* append (config) = Status
         reads the files in config in order, stopping at the first error.
      *)
      and append (pwdir, sources) =
	  (if pwdir = OS.FileSys.getDir () (* allow shorter messages if safe *)
	     then List.foldl loadAbort OK sources
	   else List.foldl loadAbort OK
	        (List.map (fn p => OS.Path.mkAbsolute (p, pwdir)) sources))

      fun define (sources) = (OS.FileSys.getDir (), sources)

    end  (* structure Config *)

    (* make (configFile)
       read and then load configuration from configFile
    *)
    fun make (fileName) = Config.load (Config.read fileName)
  in

    (* re-exporting environment parameters and utilities defined elsewhere *)
    structure Print :
      sig
	val implicit : bool ref		(* false, print implicit args *)
	val depth : int option ref	(* NONE, limit print depth *)
	val length : int option ref	(* NONE, limit argument length *)
	val indent : int ref		(* 3, indentation of subterms *)
	val width : int ref		(* 80, line width *)
        val sgn : unit -> unit		(* print signature *)
        val prog : unit -> unit		(* print signature as program *)
	val subord : unit -> unit       (* print subordination relation *)
        structure TeX :			(* print in TeX format *)
	sig
	  val sgn : unit -> unit	(* print signature *)
	  val prog : unit -> unit	(* print signature as program *)
	end
      end
    =
    struct
      val implicit = Print.implicit
      val depth = Print.printDepth
      val length = Print.printLength
      val indent = Print.Formatter.Indent
      val width = Print.Formatter.Pagewidth
      fun sgn () = Print.printSgn ()
      fun prog () = ClausePrint.printSgn ()
      fun subord () = Subordinate.show ()
      structure TeX =
      struct
	fun sgn () = printSgnTeX ()
	fun prog () = printProgTeX ()
      end

(*      structure Table =
	struct
	  fun print () = TableIndex.printTable ()
          fun printEntries () = TableIndex.printTableEntries()
	end

*)
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
      val optimize : bool ref
    end
    =
    struct
      val optimize = Compile.optimize
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

    datatype Status = datatype Status
    val reset = reset
    val loadFile = loadFile
    val readDecl = readDecl
    val decl = decl

    val top = top

    structure Config :
      sig
	type config			(* configuration *)
        val suffix : string ref         (* suffix of configuration files *)
	val read : string -> config	(* read configuration from config file *)
	val load : config -> Status	(* reset and load configuration *)
	val append : config -> Status	(* load configuration (w/o reset) *)
	val define : string list -> config  (* explicitly define configuration *)
      end
    = Config
    val make = make

    val version = "Twelf 1.3R4, June 20, 2002 (with world, coverage, and totality checking)"

    structure Table : 
      sig 
	datatype Strategy = datatype TableIndex.Strategy
	val strategy : Strategy ref
	val strengthen : bool ref
	val top : unit -> unit
      end 
    = 
  struct
    datatype Strategy = datatype TableIndex.Strategy
    val strategy = TableIndex.strategy
    val strengthen = TableIndex.strengthen
      	  
    (* top () = () starts interactive query loop *)
    fun top () = 
      let 
	fun sLoopT () = if Solve.qLoopT () then OK else ABORT
      
	fun topLoopT () = 
	  case (handleExceptions "stdIn" sLoopT) () (* "stdIn" as fake fileName *)
	    of ABORT => topLoopT ()
	  | OK => ()
      in 
	topLoopT ()
      end 
  end

  end  (* local *)
end; (* functor Twelf *)
