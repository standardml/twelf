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

(*
structure Assign =
  Assign (structure IntSyn' = IntSyn
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail);
*)

structure AbsMachine = 
  AbsMachine (structure IntSyn' = IntSyn
              structure CompSyn' = CompSyn
              structure Unify = UnifyTrail
	      (* structure Assign = Assign *)
	      structure Index = Index
              structure CPrint = CPrint
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
