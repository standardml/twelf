structure Print =
  Print (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Names = Names
	 structure Formatter' = Formatter);

structure ClausePrint =
  ClausePrint (structure IntSyn' = IntSyn
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Formatter' = Formatter
	       structure Print = Print);
