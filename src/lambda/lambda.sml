structure IntSyn =
  IntSyn (structure Global = Global);

structure Pattern =
  Pattern (structure IntSyn' = IntSyn);

structure Whnf =
  Whnf (structure IntSyn' = IntSyn
	structure Pattern = Pattern);

structure Conv =
  Conv (structure IntSyn' = IntSyn
	structure Whnf = Whnf);

structure Constraints =
  Constraints (structure IntSyn' = IntSyn
	       structure Conv = Conv);

structure Trail = 
  Trail (structure IntSyn' = IntSyn);
  
structure NoTrail = 
  NoTrail (structure IntSyn' = IntSyn);

structure Unify =
  Unify (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Pattern = Pattern
	 structure Trail = NoTrail);

structure UnifyTrail =
  Unify (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Pattern = Pattern
	 structure Trail = Trail);

structure Abstract =
  Abstract (structure IntSyn' = IntSyn
	    structure Whnf = Whnf
	    structure Pattern = Pattern
	    structure Constraints = Constraints
	    structure Unify = Unify);
