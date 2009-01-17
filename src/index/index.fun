(* Indexing *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor Index (structure Global : GLOBAL
	       structure Queue : QUEUE
	       (*! structure IntSyn' : INTSYN !*)
		 )
  : INDEX =
struct
  (*! structure IntSyn = IntSyn' !*)
 
  local
    structure I = IntSyn

    fun cidFromHead (I.Const c) = c
      | cidFromHead (I.Def c) = c

    (* Index table                             
       Invariant: 
       For all type families  a
       indexTable (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
    structure CH = CidHashTable
    val indexTable : (IntSyn.Head Queue.queue) CH.Table = CH.new(500)

    fun reset () = CH.clear indexTable
    val lookup' = valOf o (CH.lookup indexTable)
    val update' = CH.insert indexTable

    (* update (a, c) = ()
       inserts c into the index queue for family a
       Invariant: a = target family of c
    *)
    fun update (a, c) = CH.insert indexTable (a, Queue.insert (c, lookup' a))

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
	        (update'(a, q'); l)
	in
	  lk (Queue.toList (lookup' a))
	end

    (* install (c) = ()
       installs c into the correct index queue
       presently ignores definitions
    *)
    fun install fromCS (H as I.Const c) =
        (case (fromCS, ModSyn.sgnLookup (c))
           of (_, I.ConDec (_, _, _, _, A, I.Type)) => update (cidFromHead (I.targetHead A), H)
	    | (I.Clause, I.ConDef (_, _, _, _, A, I.Type, _)) => (update (cidFromHead (I.targetHead A), I.Def(c)))
            | _ => ())
  in
    val reset = reset
    (* val resetFrom = resetFrom *)
    val install = install
    val lookup = lookup

  end (* local *)

end;  (* functor Index *)
