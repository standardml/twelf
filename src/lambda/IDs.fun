(* This structure encapsulates all data types and their methods pertaining to id's. *)
structure IDs = struct
   type lid = int                        (* local id's of (declared or imported) declarations *)
   type mid = int                        (* global id's of modules (= signatures) *)
   type cid = mid * lid                  (* global id's of declarations *)
   type qid = (cid * cid) list           (* qualified local id, this gives the path along which a declaration was imported *)
   fun cidhash(x,y) = 1000 * x + y       (* hashing cid's *)
   fun cidcompare((x,y),(x',y')) =       (* comparing cid's *)
      case Int.compare(x,x')
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => Int.compare(y,y')

   fun midcidcompare((x,y),(x',y')) =       (* comparing cid's *)
      case Int.compare(x,x')
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => cidcompare(y,y')
   fun midcidcidcompare ((x,(y1,y2)), (x',(y1',y2'))) =
      case midcidcompare((x,y1),(x',y1'))
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => cidcompare(y2,y2')
   
   fun newcid(m,c) = (m,c)               (* constructor for cid's *)
   fun midOf(m,_) = m                    (* cid field accessors *)
   fun lidOf(_,l) = l
   fun cidToString(m,l) = "(" ^ (Int.toString m) ^ "," ^ (Int.toString l) ^ ")"
   val invalidCid = (~1,~1)
   fun preimageFromQid(s : cid, nil : qid) = NONE
     | preimageFromQid(s,       (s',c) :: tl) = if s = s' then SOME c else preimageFromQid(s, tl)

(* This stuff doesn't belong here, but I didn't know where else to put it. -fr *)
   type Qid = string list
   (* get a string from a list *)
   fun mkString(nil : string list, pre, mid, post) = pre ^ post
    | mkString(a :: l, pre, mid, post) = pre ^ (foldl (fn (x,y) => y ^ mid ^ x) a l) ^ post

end

(* These tables should be moved to the others *) 
structure CidHashTable =
  HashTable (type key' = IDs.cid
             val hash = IDs.cidhash
             val eq = (op =));
structure MidHashTable = IntHashTable

structure MidRedBlackTree = IntRedBlackTree

structure CidRedBlackTree =
  RedBlackTree (type key' = IDs.cid
		val compare = IDs.cidcompare) 

structure MidCidRedBlackTree =
  RedBlackTree (type key' = IDs.mid * IDs.cid
		val compare = IDs.midcidcompare) 

structure MidCidCidRedBlackTree =
  RedBlackTree (type key' = IDs.mid * (IDs.cid * IDs.cid)
		val compare = IDs.midcidcidcompare) 
