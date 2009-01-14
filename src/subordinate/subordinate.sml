structure MemoTable =
  HashTable (type key' = IDs.cid * IDs.cid
	     val hash = (fn (n,m) => 7 * (IDs.cidhash n) + (IDs.cidhash m))
             val eq = (op =));

structure Subordinate = 
  Subordinate (structure Global = Global
	       (*! structure IntSyn' = IntSyn !*)
	       structure Whnf = Whnf
	       structure Names = Names
	       structure Table = CidRedBlackTree
	       structure MemoTable = MemoTable
	       structure IntSet = IntSet);
