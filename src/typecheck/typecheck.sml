structure TypeCheck =
  TypeCheck (structure IntSyn' = IntSyn
	     structure Conv = Conv
	     structure Whnf = Whnf
	     structure Print = Print);

structure Strict =
  Strict (structure IntSyn' = IntSyn
	  structure Paths' = Paths);
