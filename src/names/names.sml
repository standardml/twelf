structure Names =
  Names (structure Global = Global
	 structure IntSyn' = IntSyn
	 structure HashTable = StringHashTable
	 structure RedBlackTree = StringRedBlackTree
	 structure IntTree = IntRedBlackTree);
