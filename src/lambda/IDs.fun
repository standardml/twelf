structure IDs = struct
   type lid = int
   type mid = int
   type cid = mid * lid
   fun cidhash(x,y) = 1000 * x + y
   fun cidcompare((x,y),(x',y')) =
      case Int.compare(x,x')
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => Int.compare(y,y')
   type qid = lid list
   fun newcid(m,c) = (m,c)
   fun midOf(m,_) = m
   fun lidOf(_,l) = l
   fun nextMid(m) = m + 1
   fun nextLid(l) = l + 1
   fun firstMid() = 0
   fun firstLid() = 0
end

structure CidHashTable =
  HashTable (type key' = IDs.cid
             val hash = IDs.cidhash
             val eq = (op =));

structure CidRedBlackTree =
  RedBlackTree (type key' = IDs.cid
		val compare = IDs.cidcompare) 
