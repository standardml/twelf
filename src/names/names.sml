structure Names =
  Names (structure Global = Global
	 (*! structure IntSyn' = IntSyn !*)
         structure Constraints = Constraints
	 structure HashTable = StringHashTable
	 structure StringTree = StringRedBlackTree);
