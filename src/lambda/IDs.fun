(* This structure encapsulates all data types and their methods pertaining to id's. *)
structure IDs = struct
   type lid = int                        (* local id's of (declared or imported) declarations *)
   type mid = int                        (* global id's of modules (= signatures) *)
   type cid = mid * lid                  (* global id's of declarations *)
   type qid = lid list                   (* qualified local id, this gives the path along which a declaration was imported *)
   fun cidhash(x,y) = 1000 * x + y       (* hashing cid's *)
   fun cidcompare((x,y),(x',y')) =       (* comparing cid's *)
      case Int.compare(x,x')
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => Int.compare(y,y')
   fun newcid(m,c) = (m,c)               (* constructor for cid's *)
   fun midOf(m,_) = m                    (* cid field accessors *)
   fun lidOf(_,l) = l
   fun nextMid(m) = m + 1                (* simple functions to hide the implementation in terms of integers *)
   fun nextLid(l) = l + 1
   fun firstMid() = 0
   fun firstLid() = 0
   fun cidToString(m,l) = "(" ^ (Int.toString m) ^ "," ^ (Int.toString l) ^ ")"
   val invalidCid = (~1,~1)
end

(* These tables should be moved to the others *) 
structure CidHashTable =
  HashTable (type key' = IDs.cid
             val hash = IDs.cidhash
             val eq = (op =));

structure CidRedBlackTree =
  RedBlackTree (type key' = IDs.cid
		val compare = IDs.cidcompare) 
