structure MTPGlobal = 
  MTPGlobal (structure MetaGlobal = MetaGlobal)

(* Now in funsyn.fun *)
(*
structure FunSyn = 
  FunSyn ((*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf
	  structure Conv = Conv);
*)

structure StateSyn = 
  StateSyn ((*! structure FunSyn' = FunSyn !*)
	    (*! structure IntSyn' = IntSyn !*)
	    structure Whnf = Whnf
	    structure Conv = Conv)

structure FunNames = 
  FunNames (structure Global = Global
	    (*! structure FunSyn' = FunSyn !*)
	    structure HashTable = StringHashTable);

structure FunPrint = 
  FunPrint ((*! structure FunSyn' = FunSyn !*)
	    structure Formatter = Formatter
	    structure Print = Print
	    structure Names = Names);
(* moves eventually into the Twelf core *)
structure Weaken =
  Weaken ((*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf)

structure FunWeaken =
  FunWeaken ((*! structure FunSyn' = FunSyn !*)
	     structure Weaken = Weaken)

structure FunTypeCheck = 
  FunTypeCheck ((*! structure FunSyn' = FunSyn !*)
		structure StateSyn' = StateSyn
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
          (*! structure FunSyn' = FunSyn !*)
	  structure ModeTable = ModeTable
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

structure MTPData = 
  MTPData (structure MTPGlobal = MTPGlobal)

structure MTPAbstract =
  MTPAbstract ((*! structure IntSyn' = IntSyn !*)
               (*! structure FunSyn' = FunSyn !*)
	       structure StateSyn' = StateSyn
	       structure Whnf = Whnf
	       structure Constraints = Constraints
               structure Unify = UnifyTrail
	       structure Subordinate = Subordinate
	       structure TypeCheck = TypeCheck
	       structure FunTypeCheck = FunTypeCheck
	       structure Abstract = Abstract);


structure MTPInit = 
  MTPInit (structure MTPGlobal = MTPGlobal
	   (*! structure IntSyn = IntSyn !*)
	   structure Names = Names
	   (*! structure FunSyn' = FunSyn !*)
	   structure StateSyn' = StateSyn
	   structure MTPData = MTPData
	   structure Formatter = Formatter
	   structure Whnf = Whnf
	   structure Print = Print
	   structure FunPrint = FunPrint)

structure MTPrint = 
  MTPrint (structure Global = Global
	   (*! structure IntSyn = IntSyn !*)
	   (*! structure FunSyn = FunSyn !*)
	   structure Names = Names
	   structure StateSyn' = StateSyn
	   structure Formatter' = Formatter
	   structure Print = Print
	   structure FunPrint = FunPrint)



structure MTPSearch = 
  MTPSearch (structure Global = Global
             structure MTPGlobal = MTPGlobal
	     (*! structure IntSyn' = IntSyn !*)
	     structure Abstract = Abstract
	     structure Conv = Conv
	     structure StateSyn' = StateSyn
	     (*! structure CompSyn' = CompSyn !*)
	     structure Compile = Compile
	     structure Whnf = Whnf
	     structure Unify = UnifyTrail
	     structure Index = IndexSkolem
	     structure Assign = Assign 
	     structure CPrint = CPrint
	     structure Print = Print
	     structure Names = Names
             (*! structure CSManager = CSManager  !*)
	       );

structure MTPFilling =
  MTPFilling (structure MTPGlobal = MTPGlobal
              (*! structure IntSyn = IntSyn !*)
	      (*! structure FunSyn' = FunSyn !*)
	      structure StateSyn' = StateSyn
	      structure MTPData = MTPData
	      structure Whnf = Whnf
	      structure Abstract = Abstract
	      structure TypeCheck = TypeCheck
	      structure Search = MTPSearch
	      structure Whnf = Whnf)

structure MTPSplitting = 
  MTPSplitting (structure MTPGlobal = MTPGlobal
		structure Global = Global
		(*! structure IntSyn = IntSyn !*)
		(*! structure FunSyn = FunSyn !*)
		structure StateSyn' = StateSyn
		structure Heuristic = Heuristic
		structure MTPrint = MTPrint
		structure MTPAbstract = MTPAbstract
		structure Names = Names  (* to be removed -cs *)
		structure Conv = Conv
		structure Whnf = Whnf
		structure TypeCheck = TypeCheck
		structure Subordinate = Subordinate
		structure FunTypeCheck = FunTypeCheck
		structure Index = Index
		structure Print = Print
		structure Unify = UnifyTrail
                (*! structure CSManager = CSManager !*)
		  ); 

structure UniqueSearch =
  UniqueSearch (structure Global = Global
		(*! structure IntSyn' = IntSyn !*)
		(*! structure FunSyn' = FunSyn !*)
		structure StateSyn' = StateSyn
		structure Abstract = Abstract
		structure MTPGlobal = MTPGlobal
		(*! structure CompSyn' = CompSyn !*)
		structure Whnf = Whnf
		structure Unify = UnifyTrail
		structure Assign = Assign		
		structure Index = Index
		structure Compile = Compile
		structure CPrint = CPrint
		structure Print = Print
		structure Names = Names
                (*! structure CSManager = CSManager !*)
		  ); 

structure Inference = 
  Inference (structure MTPGlobal = MTPGlobal
	     (*! structure IntSyn = IntSyn !*)
	     (*! structure FunSyn' = FunSyn !*)
	     structure StateSyn' = StateSyn
	     structure Abstract = Abstract
	     structure TypeCheck = TypeCheck
	     structure FunTypeCheck = FunTypeCheck
	     structure UniqueSearch = UniqueSearch
	     structure Whnf = Whnf
	     structure Print = Print)

		  
structure MTPRecursion = 
  MTPRecursion (structure MTPGlobal = MTPGlobal
                structure Global =  Global
		(*! structure IntSyn = IntSyn !*)
		(*! structure FunSyn = FunSyn !*)
		structure StateSyn' = StateSyn
		structure FunTypeCheck = FunTypeCheck
		structure MTPSearch = MTPSearch
		structure Abstract = Abstract
		structure MTPAbstract = MTPAbstract
		structure Whnf = Whnf
		structure Unify = UnifyTrail
		structure Conv = Conv
		structure Names = Names
		structure Subordinate = Subordinate
		structure MTPrint = MTPrint
		structure Print = Print
		structure TypeCheck = TypeCheck
		structure FunPrint = FunPrint
		structure Formatter = Formatter
                (*! structure CSManager = CSManager !*)
		  ); 



structure MTPStrategy = 
  MTPStrategy (structure MTPGlobal = MTPGlobal
	       structure StateSyn' = StateSyn
	       structure MTPrint = MTPrint
	       structure MTPData = MTPData
	       structure MTPFilling = MTPFilling
	       structure MTPSplitting = MTPSplitting
	       structure MTPRecursion = MTPRecursion
	       structure Inference = Inference
	       structure Timers = Timers)

structure MTProver =
  MTProver (structure MTPGlobal = MTPGlobal
            (*! structure IntSyn' = IntSyn !*)
            (*! structure FunSyn = FunSyn !*)
	    structure StateSyn = StateSyn
	    structure Order = Order
	    structure MTPrint = MTPrint
	    structure MTPInit = MTPInit
	    structure MTPStrategy = MTPStrategy
	    structure RelFun = RelFun)

structure CombiProver = 
  CombiProver (structure MTPGlobal = MTPGlobal
	       (*! structure IntSyn' = IntSyn !*)
	       structure ProverNew = MTProver
	       structure ProverOld = Prover)


structure MTPi = 
  MTPi (structure MTPGlobal = MTPGlobal
	(*! structure IntSyn = IntSyn !*)
	(*! structure FunSyn' = FunSyn !*)
	structure StateSyn' = StateSyn
	structure FunTypeCheck = FunTypeCheck
	structure RelFun = RelFun
	structure Formatter = Formatter
	structure Print = Print
	structure MTPrint = MTPrint
	structure MTPInit = MTPInit
	structure MTPFilling = MTPFilling
	structure MTPData = MTPData
	structure MTPSplitting = MTPSplitting
	structure MTPRecursion = MTPRecursion
	structure Inference = Inference
	structure MTPStrategy = MTPStrategy
	structure Names = Names
	structure Order = Order
	structure Timers = Timers
	structure Ring = Ring)
	  