(* structure ModeSyn  in modesyn.sml *)

structure ModeTable =
  ModeTable (structure Table = IntRedBlackTree);

structure ModeDec =
  ModeDec ((*! structure ModeSyn' = ModeSyn !*)
	   (*! structure Paths' = Paths !*)
	     );

structure ModeCheck =
  ModeCheck ((*! structure IntSyn = IntSyn !*)
	     structure ModeTable = ModeTable
             structure Whnf = Whnf
	     structure Index = Index
	     (*! structure Paths = Paths !*)
	     structure Origins = Origins);

structure ModePrint =
  ModePrint ((*! structure ModeSyn' = ModeSyn !*)
	     structure Names = Names
	     structure Formatter = Formatter
	     structure Print = Print);
