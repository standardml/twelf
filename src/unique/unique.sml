structure UniqueTable =
  ModeTable (structure Table = IntRedBlackTree);

structure UniqueCheck =
  ModeCheck (structure ModeTable = UniqueTable
             structure Whnf = Whnf
	     structure Index = Index
	     structure Origins = Origins);

structure Unique =
  Unique (structure Global = Global
	  structure Whnf = Whnf
	  structure Abstract = Abstract
	  structure Unify = UnifyTrail
	  structure Constraints = Constraints
	  structure UniqueTable = UniqueTable
	  structure UniqueCheck = UniqueCheck
	  structure Index = Index
	  structure Subordinate = Subordinate
	  structure WorldSyn = WorldSyn
	  structure Names = Names
	  structure Print = Print
	  structure TypeCheck = TypeCheck
	  structure Timers = Timers);
