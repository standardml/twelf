(* Indexing *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor Index (structure Global : GLOBAL
	       structure Queue : QUEUE
	       structure IntSyn': INTSYN)
  : INDEX =
struct
  structure IntSyn = IntSyn'
 
  local
    structure I = IntSyn

    (* Index array                             

       Invariant: 
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
    val indexArray : (IntSyn.cid Queue.queue) Array.array =
        Array.array (Global.maxCid + 1, Queue.empty)

    (* reset () = ()
       Empties index array
    *)
    fun reset () = Array.modify (fn _ => Queue.empty) indexArray
      
    (* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *)
    fun update (a, c) =
        Array.update (indexArray, a,
		      Queue.insert (c, Array.sub (indexArray, a)))

    (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)
    fun install (c) =
        case I.sgnLookup (c)
	  of I.ConDec (_, _, A, I.Type) => update (I.targetFam A, c)
	   | _ => ()

    (* lookup a = [c1,...,cn] *)
    (*
       c1,...,cn are all constants with target family a
       in order of declaration, defined constants are omitted.

       A second lookup after the first without intermediate inserts will
       be in constant time.
    *)
    fun lookup a =
        let fun lk (l, NONE) = l
	      | lk (l, SOME(q')) =
	        (Array.update (indexArray, a, q'); l)
	in
	  lk (Queue.toList (Array.sub (indexArray, a)))
	end

  in

    val reset = reset
    val install = install
    val lookup = lookup

  end (* local *)

end;  (* functor Index *)
