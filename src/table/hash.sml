(* Hash Tables *)
(* Author: Frank Pfenning *)

functor HashTable
  (type key'
   val hash : key' -> int
   val eq : key' * key' -> bool)
  :> TABLE where type key = key' =
struct
  type key = key'
  type 'a entry = key * 'a

  (* A hashtable bucket is a linked list of mutable elements *)
  (* A hashtable is an array of buckets containing entries paired with hash values *)
  datatype 'a bucket = Nil | Cons of 'a ref * ('a bucket) ref
  type 'a Table = ((int * 'a entry) bucket) array * int

  fun new (n) = (Array.array (n,Nil), n)

  fun insertShadow (a,n) (e as (key, datum)) =
      let
	val hashVal = hash key
	val index = hashVal mod n
	val bucket = Array.sub (a, index)
	fun insertB (Cons(r' as ref(hash', e' as (key', datum')), br')) =
	    if hashVal = hash' andalso eq (key, key')
	       then (r' := (hashVal, e); SOME (e'))
	    else insertBR (br')
	and insertBR (br as ref(Nil)) =
	      (br := Cons (ref (hashVal, e), ref Nil); NONE)
	  | insertBR (br) = insertB (!br)
	fun insertA (Nil) =
	    (Array.update (a, index, Cons (ref (hashVal,e), ref Nil));
	     NONE)
	  | insertA (bucket) = insertB (bucket)
      in
	insertA bucket
      end

  fun insert h e = (insertShadow h e; ())

  fun lookup (a,n) key =
      let
	val hashVal = hash key
	fun lookup' (Cons(ref(hash1, (key1, datum1)), br)) =
	    if hashVal = hash1 andalso eq (key, key1)
	      then SOME(datum1)
	    else lookup' (!br)
	  | lookup' (Nil) = NONE
	val bucket = Array.sub (a, hashVal mod n)
      in
	lookup' bucket
      end

  fun clear (a,n) = Array.modify (fn _ => Nil) a

  fun appBucket f (Nil) = ()
    | appBucket f (Cons(ref(_, e), br)) =
        (f e; appBucket f (!br))

  fun app f (a,n) = Array.app (appBucket f) a
end;  (* functor HashTable *)

signature STRING_HASH =
sig
  val stringHash : string -> int
end;

structure StringHash :> STRING_HASH =
struct
  fun stringHash (s) =
      (* sample 4 characters from string *)
      let
	fun num (i) = Char.ord (String.sub (s,i)) mod 128
	val n = String.size (s)
      in
	if n = 0 then 0
	else let
	       val a = n-1
	       val b = n div 2
	       val c = b div 2
	       val d = b + c
	     in
	       num(a)+128*(num(b)+128*(num(c)+128*num(d)))
	     end
      end
end;  (* structure StringHash *)

structure StringHashTable
  :> TABLE where type key = string =
  HashTable (type key' = string
	     val hash = StringHash.stringHash
	     val eq = (op =));
