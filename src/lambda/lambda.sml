structure IntSyn =
  IntSyn (structure Global = Global);

structure Whnf =
  Whnf (structure IntSyn' = IntSyn);

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
	 structure Trail = NoTrail);

structure UnifyTrail =
  Unify (structure IntSyn' = IntSyn
	 structure Whnf = Whnf
	 structure Trail = Trail);

structure Abstract =
  Abstract (structure IntSyn' = IntSyn
	    structure Whnf = Whnf
	    structure Constraints = Constraints
	    structure Unify = Unify);
