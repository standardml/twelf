structure UniqueTable =
  ModeTable (structure Table = IntRedBlackTree);

structure Unique =
  Unique (structure Global = Global
	  structure Whnf = Whnf
	  structure Abstract = Abstract
	  structure Unify = UnifyTrail
	  structure Constraints = Constraints
	  structure UniqueTable = UniqueTable
	  structure Index = Index
	  structure Subordinate = Subordinate
	  structure WorldSyn = WorldSyn
	  structure Names = Names
	  structure Print = Print
	  structure TypeCheck = TypeCheck
	  structure Timers = Timers);
