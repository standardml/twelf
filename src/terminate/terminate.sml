
structure Checking = 
  Checking (structure Global = Global
	  (*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf
	  structure Conv = Conv
	  structure Unify = UnifyTrail
	  structure Trail = Trail
	  structure Names = Names
	  structure Index = Index
	  structure Subordinate = Subordinate
	  structure Formatter = Formatter
	  structure Print = Print
	  structure Order = Order
	  structure Paths = Paths
	  structure Origins = Origins
	  (*! structure CSManager = CSManager !*)
	      );


structure Reduces =
  Reduces (structure Global = Global
	  (*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf
	  structure Names = Names
	  structure Index = Index
	  structure Subordinate = Subordinate
	  structure Formatter = Formatter
	  structure Print = Print
	  structure Order = Order
	  structure Checking = Checking 
	  structure Paths = Paths
	  structure Origins = Origins
	  (*! structure CSManager = CSManager !*)
	     );

