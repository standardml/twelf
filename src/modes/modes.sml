structure ModeSyn = 
  ModeSyn (structure IntSyn' = IntSyn
	   structure Names = Names
	   structure Table = IntRedBlackTree
	   structure Index = Index);

structure ModeDec =
  ModeDec (structure ModeSyn' = ModeSyn
	   structure Paths' = Paths);

structure ModeCheck =
  ModeCheck (structure ModeSyn' = ModeSyn
	     structure Paths' = Paths);

structure ModePrint =
  ModePrint (structure ModeSyn' = ModeSyn
	     structure Names = Names
	     structure Formatter = Formatter
	     structure Print = Print);
