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

structure FVars =
  FVars (structure IntSyn' = IntSyn
         structure Names = Names);

structure EVars =
  EVars (structure IntSyn' = IntSyn
         structure Names = Names);

structure TpRecon =
  TpRecon (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure Strict = Strict
	   structure Print = Print
	   structure Timers = Timers
           structure Vars = FVars);

structure TpTrace =
  TpTrace (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure Strict = Strict
	   structure Print = Print
	   structure Timers = Timers
           structure Vars = FVars);

structure TpReconQ =
  TpRecon (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure Strict = Strict
	   structure Print = Print
	   structure Timers = Timers
           structure Vars = EVars);

structure TpTraceQ =
  TpTrace (structure Global = Global
	   structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Paths' = Paths
 	   structure Whnf = Whnf
	   structure Unify = Unify
	   structure Abstract = Abstract
	   structure TypeCheck = TypeCheck
	   structure Strict = Strict
	   structure Print = Print
	   structure Timers = Timers
           structure Vars = EVars);

structure ModeRecon =
  ModeRecon (structure Global = Global
	     structure IntSyn = IntSyn
	     structure ModeSyn' = ModeSyn
	     structure ModeDec = ModeDec
	     structure Whnf = Whnf
	     structure Paths' = Paths
	     structure ModePrint = ModePrint
	     structure TpRecon' = TpTrace);

structure ThmRecon =
  ThmRecon (structure Global = Global
	    structure IntSyn = IntSyn
	    structure ModeSyn = ModeSyn
	    structure ThmSyn' = ThmSyn
	    structure Names = Names
	    structure TpRecon' = TpTrace
	    structure Paths' = Paths);

structure ParseTerm =
  ParseTerm (structure Parsing' = Parsing
	     structure ExtSyn' = TpTrace
	     structure Names = Names);

structure ParseTermQ =
  ParseTerm (structure Parsing' = Parsing
	     structure ExtSyn' = TpTraceQ
	     structure Names = Names);

structure ParseConDec =
  ParseConDec (structure Parsing' = Parsing
	      structure ExtSyn' = TpTrace
	      structure ParseTerm = ParseTerm);

structure ParseQuery =
  ParseQuery (structure Parsing' = Parsing
	      structure ExtSyn' = TpTraceQ
	      structure ParseTerm = ParseTermQ);

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

structure Parser =
  Parser (structure Parsing' = Parsing
	  structure Stream' = Stream
	  structure ExtSyn' = TpTrace
	  structure ExtSynQ' = TpTraceQ
	  structure Names' = Names
	  structure ExtModes' = ModeRecon
	  structure ThmExtSyn' = ThmRecon
	  structure ParseConDec = ParseConDec
	  structure ParseQuery = ParseQuery
	  structure ParseFixity = ParseFixity
	  structure ParseMode = ParseMode
	  structure ParseThm = ParseThm
          structure ParseTermQ = ParseTermQ);

structure Solve =
  Solve (structure Global = Global
	 structure IntSyn' = IntSyn
	 structure Names = Names
	 structure Parser = Parser
	 structure Constraints = Constraints
	 structure Abstract = Abstract
	 structure TpReconQ = TpTraceQ
	 structure Timers = Timers
	 structure CompSyn = CompSyn
	 structure Compile = Compile
	 structure Trail = Trail
	 structure AbsMachine = TMachine
	 structure Print = Print);

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
	 structure TpReconQ = TpTraceQ
	 structure TpRecon = TpTrace 

	 structure ModeSyn = ModeSyn
	 structure ModeCheck = ModeCheck
	 structure ModeDec = ModeDec
	 structure ModeRecon = ModeRecon
	 structure ModePrint = ModePrint

	 structure Terminate = Terminate

	 structure Index = Index
	 structure IndexSkolem = IndexSkolem
	 structure Subordinate = Subordinate
	 structure CompSyn' = CompSyn
	 structure Compile = Compile
	 structure Trail = Trail
	 structure AbsMachine = TMachine
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

         structure Trace = Trace

	 structure PrintTeX = PrintTeX
	 structure ClausePrintTeX = ClausePrintTeX);
