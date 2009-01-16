structure TabledSyn = 
  TabledSyn ((*! structure IntSyn' = IntSyn !*)
	   structure Names = Names
	   structure Table = CidRedBlackTree
	   structure Index = Index);
