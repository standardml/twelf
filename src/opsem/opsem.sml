structure CompSyn =
  CompSyn (structure Global = Global
           structure IntSyn' = IntSyn
	   structure Names = Names);

structure Compile =
  Compile (structure IntSyn' = IntSyn
	   structure CompSyn' = CompSyn
	   structure Whnf = Whnf);

structure CPrint =
  CPrint (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Print = Print
	  structure Formatter = Formatter
	  structure Names = Names);

structure AbsMachine = 
  AbsMachine (structure IntSyn' = IntSyn
              structure CompSyn' = CompSyn
              structure Unify = UnifyTrail
              structure Trail = Trail
              structure CPrint = CPrint
              structure Names = Names); 
