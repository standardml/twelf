(* Front End Interface *)
(* Author: Frank Pfenning *)

(* Presently, we do not memoize the token stream returned *)
(* by the lexer.  Use Stream = MStream below if memoization becomes *)
(* necessary. *)
structure Lexer =
  Lexer (structure Stream' = Stream
	 structure Paths' = Paths);

structure Parsing =
  Parsing (structure Stream' = Stream
	   structure Lexer' = Lexer);

structure TpRecon =
  TpRecon (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Unify = UnifyNoTrail
	   structure Abstract = Abstract
	   structure Constraints = Constraints
	   structure TypeCheck = TypeCheck
           structure Conv = Conv
	   structure Strict = Strict
	   structure Print = Print
	   structure Timers = Timers
           structure CSManager = CSManager);

structure DefineRecon =
  DefineRecon (structure IntSyn' = IntSyn
               structure Names = Names
               structure TpRecon' = TpRecon
               structure Paths' = Paths);

structure ModeRecon =
  ModeRecon (structure Global = Global
	     structure IntSyn = IntSyn
	     structure ModeSyn' = ModeSyn
	     structure ModeDec = ModeDec
	     structure Whnf = Whnf
	     structure Paths' = Paths
             structure Names = Names
	     structure ModePrint = ModePrint
	     structure TpRecon' = TpRecon);

structure ThmRecon =
  ThmRecon (structure Global = Global
	    structure IntSyn = IntSyn
	    structure Abstract = Abstract
	    structure Constraints = Constraints
	    structure ModeSyn = ModeSyn
	    structure ThmSyn' = ThmSyn
	    structure Names = Names
	    structure TpRecon' = TpRecon
	    structure Paths' = Paths
	    structure Print = Print);

structure ModRecon =
  ModRecon (structure Global = Global
            structure IntSyn = IntSyn
            structure Names = Names
            structure Paths' = Paths
            structure TpRecon' = TpRecon
            structure ModSyn' = ModSyn
            structure IntTree = IntRedBlackTree);

structure ParseTerm =
  ParseTerm (structure Parsing' = Parsing
	     structure ExtSyn' = TpRecon
	     structure Names = Names);

structure ParseConDec =
  ParseConDec (structure Parsing' = Parsing
	      structure ExtSyn' = TpRecon
	      structure ParseTerm = ParseTerm);

structure ParseDefine =
  ParseDefine (structure Parsing' = Parsing
	       structure ExtDefine' = DefineRecon
	       structure Paths = Paths
	       structure ParseTerm = ParseTerm);

structure ParseQuery =
  ParseQuery (structure Parsing' = Parsing
	      structure ExtSyn' = TpRecon
	      structure ParseTerm = ParseTerm);

structure ParseFixity =
  ParseFixity (structure Parsing' = Parsing
	       structure Names' = Names);

structure ParseMode =
  ParseMode (structure Parsing' = Parsing
	     structure ExtModes' = ModeRecon
	     structure Paths = Paths
	     structure ParseTerm = ParseTerm);

structure ParseThm =
  ParseThm (structure Parsing' = Parsing
	    structure ThmExtSyn' = ThmRecon
	    structure ParseTerm = ParseTerm
	    structure Paths = Paths);

structure ParseModules =
  ParseModules (structure Parsing' = Parsing
                structure ModExtSyn' = ModRecon
                structure ParseTerm = ParseTerm
                structure Paths = Paths);

structure Parser =
  Parser (structure Parsing' = Parsing
	  structure Stream' = Stream
	  structure ExtSyn' = TpRecon
          structure ExtDefine' = DefineRecon
	  structure Names' = Names
	  structure ExtModes' = ModeRecon
	  structure ThmExtSyn' = ThmRecon
          structure ModExtSyn' = ModRecon
	  structure ParseConDec = ParseConDec
          structure ParseDefine = ParseDefine
	  structure ParseQuery = ParseQuery
	  structure ParseFixity = ParseFixity
	  structure ParseMode = ParseMode
	  structure ParseThm = ParseThm
          structure ParseModules = ParseModules
          structure ParseTerm = ParseTerm);

structure Solve =
  Solve (structure Global = Global
	 structure IntSyn' = IntSyn
 	 structure Whnf = Whnf
	 structure Names = Names
	 structure Parser = Parser
	 structure Constraints = Constraints
	 structure Abstract = Abstract
	 structure Unify = UnifyNoTrail
	 structure TpRecon = TpRecon
         structure DefineRecon = DefineRecon
	 structure Timers = Timers
	 structure CompSyn = CompSyn
	 structure Compile = Compile
	 structure CPrint = CPrint
	 structure AbsMachine = SwMachine
	 structure Tabled = Tabled
	 structure PtRecon = PtRecon
	 structure TableIndex = TableIndex
	 structure Strict = Strict
	 structure Print = Print
         structure CSManager = CSManager);

structure Twelf =
  Twelf (structure Global = Global
	 structure Timers = Timers
	 structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Print = Print

	 structure Names = Names
	 structure Paths = Paths
	 structure Origins = Origins
	 structure Lexer = Lexer
	 structure Parsing = Parsing
	 structure Parser = Parser
	 structure TypeCheck = TypeCheck
	 structure Strict = Strict
	 structure Constraints = Constraints
	 structure Abstract = Abstract
	 structure TpRecon = TpRecon 

         structure DefineRecon = DefineRecon

	 structure ModeSyn = ModeSyn
	 structure ModeCheck = ModeCheck
	 structure ModeDec = ModeDec
	 structure ModeRecon = ModeRecon
	 structure ModePrint = ModePrint

         structure Cover = Cover
         structure Total = Total

	 structure Terminate = Terminate
	 structure Reduces = Reduces

	 structure Index = Index
	 structure IndexSkolem = IndexSkolem
	 structure Subordinate = Subordinate
	 structure CompSyn' = CompSyn
	 structure Compile = Compile
	 structure CPrint = CPrint
	 structure AbsMachine = SwMachine
	 structure Tabled = Tabled
	 structure TableIndex = TableIndex
	 structure Solve = Solve

	 structure ThmSyn = ThmSyn
	 structure Thm = Thm
	 structure ThmRecon = ThmRecon
	 structure ThmPrint = ThmPrint
	 structure MetaGlobal = MetaGlobal
	 structure FunSyn = FunSyn
	 structure Skolem = Skolem
	 structure Prover = CombiProver
	 structure ClausePrint = ClausePrint

	 structure TabledSyn = TabledSyn

         structure ModSyn = ModSyn
         structure ModRecon = ModRecon

	 structure WorldSyn = WorldSyn
	 structure WorldPrint = WorldPrint

         structure Trace = Trace

	 structure PrintTeX = PrintTeX
	 structure ClausePrintTeX = ClausePrintTeX

         structure CSManager = CSManager);
