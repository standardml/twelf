structure TabledSyn = 
  TabledSyn ((*! structure IntSyn' = IntSyn !*)
	   structure Names = Names
	   structure Table = IntRedBlackTree
	   structure Index = Index);
