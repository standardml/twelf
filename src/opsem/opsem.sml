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
              structure Trail = Trail
              structure CPrint = CPrint
              structure Names = Names); 
