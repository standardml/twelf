structure CompSyn =
  CompSyn (structure Global = Global
           structure IntSyn' = IntSyn
	   structure Names = Names);

structure Compile =
  Compile (structure IntSyn' = IntSyn
	   structure CompSyn' = CompSyn
	   structure Whnf = Whnf
	   structure TypeCheck = TypeCheck
	   structure Names = Names);

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
	      (* structure Assign = Assign *)
	      structure Index = Index
              structure CPrint = CPrint
              structure Names = Names
              structure CSManager = CSManager); 

(*
structure Assign =
  Assign (structure IntSyn' = IntSyn
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail);
*)

structure AbstractTabled =
  AbstractTabled (structure IntSyn' = IntSyn
		  structure Whnf = Whnf
		  structure Constraints = Constraints
		  structure Unify = UnifyTrail
		  structure Subordinate = Subordinate);

structure TableIndex = 
  TableIndex (structure Global = Global
	      structure Queue = Queue
	      structure IntSyn' = IntSyn
	      structure CompSyn' = CompSyn
	      structure Conv = Conv
	      structure Unify = UnifyTrail 
	      structure AbstractTabled = AbstractTabled
	      structure Whnf = Whnf
	      structure Print = Print
	      structure CPrint = CPrint
	      structure TypeCheck = TypeCheck);

structure Tabled = 
  Tabled (structure IntSyn' = IntSyn
	  structure CompSyn' = CompSyn
	  structure Unify = UnifyTrail 
	  structure Whnf = Whnf
	  (* structure Assign = Assign *)
	  structure Index = Index
	  structure Queue = Queue
	  structure TableIndex = TableIndex
	  structure AbstractTabled = AbstractTabled
	  structure CPrint = CPrint
	  structure Print = Print
	  structure Names = Names
	  structure CSManager = CSManager); 

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
	    structure CPrint = CPrint
            structure Names = Names
	    structure Trace = Trace
              structure CSManager = CSManager);
