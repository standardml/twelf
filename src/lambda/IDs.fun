(* data types for IDs *)
(* these types are the only part of the module system that must exist for intsyn *)
(* Florian Rabe and Carsten Schürmann *)

(* This signature was supposed to be used to make the id type definitions abstract,
   but it turned out I can't enforce that with SMLNJ. So it's not used for now. -fr *)
signature IDTYPES = sig
   (* local id's of (declared or imported) declarations (= constants or structures) *)
   eqtype lid
   (* global id's of modules (= signatures or views) *)
   eqtype mid
   (* global id's of declarations, most reasonably cid = mid * lid  but left abstract for future extensions *)
   eqtype cid
   val newcid : mid * lid -> cid
   val midOf : cid -> mid
   val lidOf : cid -> lid
   val invalidCid : cid
   (* hashing cid's *)
   val cidhash : cid -> int
   (* comparing cid's *)
   val cidcompare : cid * cid -> order
   (* printing cid's *)
   val cidToString : cid -> string
end

(* This structure encapsulates all data types and their methods pertaining to id's. *)
structure IDs = struct
   (* should be idtypes : IDTYPES, see above -fr *)
   structure idtypes = struct
      type lid = int
      type mid = int                        
      type cid = mid * lid                  
      fun newcid(m,c) = (m,c)
      fun midOf(m,_) = m
      fun lidOf(_,l) = l
      val invalidCid = (~1,~1)
      fun cidhash(x,y) = 1000 * x + y
      fun cidcompare((x,y),(x',y')) =       (* comparing cid's *)
         case Int.compare(x,x')
           of LESS => LESS
            | GREATER => GREATER
            | EQUAL => Int.compare(y,y')
      fun cidToString(m,l) = "(" ^ (Int.toString m) ^ "," ^ (Int.toString l) ^ ")"
   end
   open idtypes

   (* convenience methods *)
   fun midcidcompare((x,y),(x',y')) =
      case Int.compare(x,x')
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => cidcompare(y,y')
   fun midcidcidcompare ((x,(y1,y2)), (x',(y1',y2'))) =
      case midcidcompare((x,y1),(x',y1'))
        of LESS => LESS
         | GREATER => GREATER
         | EQUAL => cidcompare(y2,y2')
   
   type qid = (cid * cid) list           (* qualified local id, this gives the path along which a declaration was imported *)
   fun preimageFromQid(s : cid, nil : qid) = NONE
     | preimageFromQid(s,    (s',c) :: tl) = if s = s' then SOME c else preimageFromQid(s, tl)

   (* methods for external IDs *)
   (* get a string from a list *)
   fun mkString(nil : string list, pre, mid, post) = pre ^ post
    | mkString(a :: l, pre, mid, post) = pre ^ (foldl (fn (x,y) => y ^ mid ^ x) a l) ^ post
   (* Qualified names (m,l) are represented as string list with "" separating
      m and l. This corresponds to using ".." as the separator. splitName retrieves the components. *)
   fun splitName names =
      let fun aux(left, nil) = (nil,left)
            | aux(left, name :: names) =
               if name = "" then (left, names) else aux(left @ [name], names)
      in  aux(nil, names)
      end
   fun parseQName(name : string) = String.fields (fn c => c = #".") name
   fun parseFQName(name : string) = splitName (parseQName name)
   val sep = "."
   val Sep = ".."
   fun foldQName l = mkString(l,"",sep,"")
   fun foldFQName(m, l) = foldQName m ^ Sep ^ foldQName l

   type Qid = string list
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
