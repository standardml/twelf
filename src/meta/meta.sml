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

(* Functor instantiation for the Prover *)
structure StateSyn = 
  StateSyn (structure FunSyn' = FunSyn
	    structure IntSyn' = IntSyn)

structure MTPAbstract =
  MTPAbstract (structure IntSyn' = IntSyn
	       structure StateSyn' = StateSyn
	       structure Whnf = Whnf
	       structure Constraints = Constraints
	       structure Subordinate = Subordinate
	       structure Trail = Trail);


structure MTPInit = 
  MTPInit (structure MTPGlobal = MTPGlobal
	   structure IntSyn = IntSyn
	   structure Names = Names
	   structure FunSyn' = FunSyn
	   structure StateSyn' = StateSyn
	   structure Formatter = Formatter
	   structure Whnf = Whnf
	   structure Print = Print
	   structure FunPrint = FunPrint)

structure MTPrint = 
  MTPrint (structure IntSyn = IntSyn
	   structure FunSyn = FunSyn
	   structure Names = Names
	   structure StateSyn' = StateSyn
	   structure Formatter' = Formatter
	   structure Print = Print
	   structure FunPrint = FunPrint)



structure MTPSearch = 
  MTPSearch (structure Global = Global
             structure MTPGlobal = MTPGlobal
	     structure IntSyn' = IntSyn
	     structure Conv = Conv
	     structure StateSyn' = StateSyn
	     structure CompSyn' = CompSyn
	     structure Compile = Compile
	     structure Whnf = Whnf
	     structure Unify = UnifyTrail
	     structure Index = IndexSkolem
	     (* structure Assign = Assign *)
	     structure Trail = Trail
	     structure CPrint = CPrint
	     structure Print = Print
	     structure Names = Names); 

structure MTPFilling =
  MTPFilling (structure IntSyn = IntSyn
	      structure FunSyn = FunSyn
	      structure StateSyn' = StateSyn
	      structure Search = MTPSearch
	      structure Whnf = Whnf)


structure MTPSplitting = 
  MTPSplitting (structure MTPGlobal = MTPGlobal
		structure Global = Global
		structure IntSyn = IntSyn
		structure FunSyn = FunSyn
		structure StateSyn' = StateSyn
		structure MTPrint = MTPrint
		structure MTPAbstract = MTPAbstract
		structure Whnf = Whnf
		structure TypeCheck = TypeCheck
		structure Index = Index
		structure Print = Print
		structure Unify = UnifyTrail)

structure MTPRecursion = 
  MTPRecursion (structure Global =  Global
		structure IntSyn = IntSyn
		structure FunSyn = FunSyn
		structure StateSyn' = StateSyn
		structure Whnf = Whnf
		structure Unify = UnifyTrail
		structure Conv = Conv
		structure Trail = Trail
		structure Names = Names
		structure Subordinate = Subordinate
		structure Print = Print
		structure FunPrint = FunPrint
		structure Formatter = Formatter)

structure MTProver =
  MTProver (structure FunSyn' = FunSyn
	    structure StateSyn' = StateSyn
	    structure MTPrint = MTPrint
	    structure MTPInit = MTPInit
	    structure MTPFilling = MTPFilling
	    structure MTPSplitting = MTPSplitting
	    structure MTPRecursion = MTPRecursion)

