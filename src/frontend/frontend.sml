(* Front End Interface *)
(* Author: Frank Pfenning *)

(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
(* Now in lexer.fun *)
(*
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);
*)

(* Now in parsing.fun *)
(*
structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);
*)


structure ReconTerm =
  ReconTerm ((*! structure IntSyn' = IntSyn !*)
	     structure Names = Names
	     (*! structure Paths' = Paths !*)
             structure Approx = Approx
 	     structure Whnf = Whnf
	     structure Unify = UnifyTrail
             structure Abstract = Abstract
	     structure Print = Print
             (*! structure CSManager = CSManager !*)
             structure StringTree = StringRedBlackTree
             structure Msg = Msg);

structure ReconConDec =
  ReconConDec (structure Global = Global
               (*! structure IntSyn' = IntSyn !*)
               structure Names = Names
               structure Abstract = Abstract
               (*! structure Paths' = Paths !*)
               structure ReconTerm' = ReconTerm
               structure Constraints = Constraints
               structure Strict = Strict
               structure TypeCheck = TypeCheck
               structure Timers = Timers
               structure Print = Print
	       structure Msg = Msg);
                                                        
structure ReconQuery =
  ReconQuery (structure Global = Global
              (*! structure IntSyn' = IntSyn !*)
              structure Names = Names
              structure Abstract = Abstract
              (*! structure Paths' = Paths !*)
              structure ReconTerm' = ReconTerm
              structure TypeCheck = TypeCheck
              structure Strict = Strict
              structure Timers = Timers
              structure Print = Print);

structure ReconMode =
  ReconMode (structure Global = Global
	     (*! structure ModeSyn' = ModeSyn !*)
	     structure Whnf = Whnf
	     (*! structure Paths' = Paths !*)
             structure Names = Names
	     structure ModePrint = ModePrint
	     structure ModeDec = ModeDec
	     structure ReconTerm' = ReconTerm);

structure ReconThm =
  ReconThm (structure Global = Global
	    structure IntSyn = IntSyn
	    structure Abstract = Abstract
	    structure Constraints = Constraints
	    (*! structure ModeSyn = ModeSyn !*)
	    structure Names = Names
	    (*! structure Paths' = Paths !*)
	    structure ThmSyn' = ThmSyn
	    structure ReconTerm' = ReconTerm
	    structure Print = Print);


structure ReconModule =
  ReconModule (structure Global = Global
               structure IntSyn = IntSyn
               structure Names = Names
               (*! structure Paths' = Paths !*)
               structure ReconTerm' = ReconTerm
               structure ModSyn' = ModSyn
               structure IntTree = IntRedBlackTree);

structure ParseTerm =
  ParseTerm ((*! structure Parsing' = Parsing !*)
	     structure ExtSyn' = ReconTerm
	     structure Names = Names);

structure ParseConDec =
  ParseConDec ((*! structure Parsing' = Parsing !*)
	       structure ExtConDec' = ReconConDec
	       structure ParseTerm = ParseTerm);

structure ParseQuery =
  ParseQuery ((*! structure Parsing' = Parsing !*)
	      structure ExtQuery' = ReconQuery
	      structure ParseTerm = ParseTerm);

structure ParseFixity =
  ParseFixity ((*! structure Parsing' = Parsing !*)
	       structure Names' = Names);

structure ParseMode =
  ParseMode ((*! structure Parsing' = Parsing !*)
	     structure ExtModes' = ReconMode
	     (*! structure Paths = Paths !*)
	     structure ParseTerm = ParseTerm);

structure ParseThm =
  ParseThm ((*! structure Parsing' = Parsing !*)
	    structure ThmExtSyn' = ReconThm
	    structure ParseTerm = ParseTerm
	    (*! structure Paths = Paths !*)
	      );

structure ParseModule =
  ParseModule ((*! structure Parsing' = Parsing !*)
               structure ModExtSyn' = ReconModule
               structure ParseTerm = ParseTerm
               (*! structure Paths = Paths !*)
		 );

structure Parser =
  Parser ((*! structure Parsing' = Parsing !*)
	  structure Stream' = Stream
	  structure ExtSyn' = ReconTerm
	  structure Names' = Names
          structure ExtConDec' = ReconConDec
          structure ExtQuery' = ReconQuery
	  structure ExtModes' = ReconMode
	  structure ThmExtSyn' = ReconThm
          structure ModExtSyn' = ReconModule
	  structure ParseConDec = ParseConDec
	  structure ParseQuery = ParseQuery
	  structure ParseFixity = ParseFixity
	  structure ParseMode = ParseMode
	  structure ParseThm = ParseThm
          structure ParseModule = ParseModule
          structure ParseTerm = ParseTerm);

structure Solve =
  Solve (structure Global = Global
	 (*! structure IntSyn' = IntSyn !*)
	 structure Names = Names
	 structure Parser = Parser
	 structure ReconQuery = ReconQuery
	 structure Timers = Timers
	 (*! structure CompSyn = CompSyn !*)
	 structure Compile = Compile
	 structure CPrint = CPrint
         (*! structure CSManager = CSManager !*)
	 structure AbsMachine = SwMachine
	 structure PtRecon = PtRecon
	 structure AbsMachineSbt = AbsMachineSbt
	 structure PtRecon = PtRecon
	 (*! structure TableParam = TableParam !*)
	 structure Tabled = Tabled
(*	 structure TableIndex = TableIndex *)
(*	 structure MemoTable = MemoTable *)
	 structure Print = Print 
         structure Msg = Msg);


structure Fquery =
  Fquery (structure Global = Global
	  structure Names = Names
	  structure ReconQuery = ReconQuery
	  structure Timers = Timers
	  structure Print = Print);

structure Twelf =
  Twelf (structure Global = Global
	 structure Timers = Timers
	 (*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Print = Print

	 structure Names = Names
	 (*! structure Paths = Paths !*)
	 structure Origins = Origins
	 structure Lexer = Lexer
	 (*! structure Parsing = Parsing !*)
	 structure Parser = Parser
	 structure TypeCheck = TypeCheck
	 structure Strict = Strict
	 structure Constraints = Constraints
	 structure Abstract = Abstract
	 structure ReconTerm = ReconTerm
         structure ReconConDec = ReconConDec
         structure ReconQuery = ReconQuery

	 structure ModeTable = ModeTable
	 structure ModeCheck = ModeCheck
	 structure ModeDec = ModeDec
	 structure ReconMode = ReconMode
	 structure ModePrint = ModePrint

         structure Unique = Unique
         structure UniqueTable = UniqueTable

         structure Cover = Cover
	 structure Converter = Converter
	 structure TomegaPrint = TomegaPrint
	 structure TomegaCoverage = TomegaCoverage
	 structure TomegaTypeCheck = TomegaTypeCheck
         structure Total = Total

	 structure Reduces = Reduces

	 structure Index = Index
	 structure IndexSkolem = IndexSkolem
	 structure Subordinate = Subordinate
	 (*! structure CompSyn' = CompSyn !*)
	 structure Compile = Compile
	 structure CPrint = CPrint
	 structure AbsMachine = SwMachine
	 (*! structure TableParam = TableParam !*)
	 structure Tabled = Tabled
	 structure Solve = Solve
	 structure Fquery = Fquery

	 structure StyleCheck = StyleCheck

	 structure ThmSyn = ThmSyn
	 structure Thm = Thm
	 structure ReconThm = ReconThm
	 structure ThmPrint = ThmPrint
                              
	 structure TabledSyn = TabledSyn

	 structure WorldSyn = WorldSyn
(*	 structure WorldPrint = WorldPrint *)
	 structure Worldify = Worldify

         structure ModSyn = ModSyn
         structure ReconModule = ReconModule

	 structure MetaGlobal = MetaGlobal
	 (*! structure FunSyn = FunSyn !*)
	 structure Skolem = Skolem
	 structure Prover = CombiProver
	 structure ClausePrint = ClausePrint

         structure Trace = Trace

	 structure PrintTeX = PrintTeX
	 structure ClausePrintTeX = ClausePrintTeX

         structure CSManager = CSManager
         structure CSInstaller = CSInstaller (* unused -- creates necessary CM dependency *)

         structure Compat = Compat
	 structure UnknownExn = UnknownExn

	 structure Msg = Msg
	   );
