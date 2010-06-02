structure SymbolAscii = SymbolAscii ();

structure SymbolTeX = SymbolTeX ();

structure Print =
  Print ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Constraints = Constraints
	 structure Names = Names
	 structure Formatter' = Formatter
	 structure Symbol = SymbolAscii);

structure ClausePrint =
  ClausePrint ((*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Formatter' = Formatter
	       structure Print = Print
	       structure Symbol = SymbolAscii);

structure PrintOMDoc =
  PrintOMDoc (structure Whnf = Whnf
	      structure Names = Names);

(* PrintTeX is outdated: It will not print modular LF correctly. *)
structure PrintTeX =
  Print ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Constraints = Constraints
	 structure Names = Names
	 structure Formatter' = Formatter
	 structure Symbol = SymbolTeX);

(* outdated - see PrintTeX *)
structure ClausePrintTeX =
  ClausePrint((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter
	      structure Print = PrintTeX
	      structure Symbol = SymbolTeX);

(* PrintTwega is outdated: It will only print the non-modular toplevel declarations *)
structure PrintTwega =
  PrintTwega ((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter);

(* removed XML printer -fr June 2010 - use OMDoc printer instead
structure PrintXML =
  PrintXML ((*! structure IntSyn' = IntSyn !*)
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure Constraints = Constraints
	      structure Names = Names
	      structure Formatter' = Formatter);

*)