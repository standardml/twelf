structure AbsMachine = 
  AbsMachine (structure IntSyn' = IntSyn
              structure CompSyn' = CompSyn
              structure Unify = UnifyTrail
	      structure Assign = Assign 
	      structure Index = Index
              structure CPrint = CPrint
              structure Print = Print
              structure Names = Names
              structure CSManager = CSManager); 

structure PtRecon = 
  PtRecon (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail
	  structure Assign = Assign 
	  structure Index = Index
	  structure CPrint = CPrint
	  structure Names = Names
	  structure CSManager = CSManager); 


structure AbstractTabled =
  AbstractTabled (structure IntSyn' = IntSyn
		  structure Print = Print
		  structure Subordinate = Subordinate
		  structure Whnf = Whnf
		  structure Constraints = Constraints
		  structure Unify = UnifyTrail
		  structure Subordinate = Subordinate
		  structure Print = Print);

structure TableIndex = 
  TableIndex (structure Global = Global
	      structure Queue = Queue
	      structure IntSyn' = IntSyn
	      structure Subordinate = Subordinate
	      structure CompSyn' = CompSyn
	      structure Conv = Conv
	      structure Unify = UnifyTrail 
	      structure AbstractTabled = AbstractTabled
	      structure Whnf = Whnf
	      structure Print = Print
	      structure CPrint = CPrint
	      structure Names = Names
	      structure TypeCheck = TypeCheck);

structure Tabled = 
  Tabled (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail 
	  structure Whnf = Whnf
	  structure TabledSyn = TabledSyn
	  structure Assign = Assign 
	  structure Subordinate = Subordinate
	  structure Index = Index
	  structure Queue = Queue
	  structure TableIndex = TableIndex
	  structure AbstractTabled = AbstractTabled
	  structure CPrint = CPrint
	  structure Print = Print
	  structure Names = Names
	  structure CSManager = CSManager
	  structure Subordinate = Subordinate); 

structure Trace =
  Trace (structure IntSyn' = IntSyn
	 structure Names = Names
	 structure Whnf = Whnf
	 structure Abstract = Abstract
	 structure Print = Print);

structure TMachine =
  TMachine (structure IntSyn' = IntSyn
	    structure CompSyn' = CompSyn
	    structure Unify = UnifyTrail
	    structure Index = Index
	    structure Assign = Assign 
	    structure CPrint = CPrint
            structure Names = Names
	    structure Trace = Trace
              structure CSManager = CSManager);

structure SwMachine =
  SwMachine (structure Trace = Trace
	     structure AbsMachine = AbsMachine
             structure TMachine = TMachine);
