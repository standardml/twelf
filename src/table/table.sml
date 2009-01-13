structure StringHashTable =
  HashTable (type key' = string
             val hash = StringHash.stringHash
             val eq = (op =));

structure IntHashTable =
  HashTable (type key' = int
             val hash = (fn n => n)
             val eq = (op =));

structure StringRedBlackTree =
  RedBlackTree (type key' = string
		val compare = String.compare) 

structure IntRedBlackTree =
  RedBlackTree (type key' = int
		val compare = Int.compare) 

structure SparseArray =
  SparseArray(structure IntTable = IntHashTable)

structure SparseArray2 =
  SparseArray2(structure IntTable = IntHashTable)


