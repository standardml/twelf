structure WorldSyn = 
  WorldSyn (structure IntSyn = IntSyn
	    structure Unify = Unify
	    structure Whnf = Whnf
	    structure Names = Names
	    structure Index = Index
	    structure CSManager = CSManager)

structure WorldPrint =
  WorldPrint (structure Global = Global
	      structure IntSyn = IntSyn
	      structure WorldSyn' = WorldSyn
	      structure Names = Names
	      structure Formatter' = Formatter
	      structure Print = Print)