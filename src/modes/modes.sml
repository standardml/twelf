structure ModeSyn = 
  ModeSyn ((*! structure IntSyn' = IntSyn !*)
	   structure Names = Names
	   structure Table = IntRedBlackTree
	   structure Index = Index);

structure ModeDec =
  ModeDec (structure ModeSyn' = ModeSyn
	   (*! structure Paths' = Paths !*)
	     );

structure ModeCheck =
  ModeCheck ((*! structure IntSyn = IntSyn *)
	     structure ModeSyn = ModeSyn
             structure Whnf = Whnf
	     structure Index = Index
	     (*! structure Paths = Paths !*)
	     structure Origins = Origins);

structure ModePrint =
  ModePrint (structure ModeSyn' = ModeSyn
	     structure Names = Names
	     structure Formatter = Formatter
	     structure Print = Print);
