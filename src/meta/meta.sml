structure FunSyn = 
  FunSyn (structure IntSyn' = IntSyn);

structure FunNames = 
  FunNames (structure Global = Global
	    structure FunSyn' = FunSyn
	    structure HashTable = StringHashTable);

structure FunPrint = 
  FunPrint (structure FunSyn' = FunSyn
	    structure Formatter = Formatter
	    structure Print = Print
	    structure Names = Names);
(* moves eventually into the Twelf core *)
structure Weaken =
  Weaken (structure IntSyn' = IntSyn
	  structure Whnf = Whnf)

structure FunWeaken =
  FunWeaken (structure FunSyn' = FunSyn
	     structure Weaken = Weaken)

structure FunTypeCheck = 
  FunTypeCheck (structure FunSyn' = FunSyn
	        structure Abstract = Abstract
	        structure TypeCheck = TypeCheck
	        structure Conv = Conv
		structure Weaken = Weaken
		structure Subordinate = Subordinate
		structure Whnf = Whnf
		structure Print = Print
		structure FunPrint = FunPrint);

structure RelFun = 
  RelFun (structure Global = Global
          structure FunSyn' = FunSyn
	  structure ModeSyn = ModeSyn
	  structure Names = Names
	  structure TypeCheck = TypeCheck
	  structure Trail = Trail
	  structure Unify = UnifyTrail
	  structure Whnf = Whnf
	  structure Print = Print
	  structure Weaken = Weaken
	  structure FunWeaken = FunWeaken
	  structure FunNames = FunNames);

