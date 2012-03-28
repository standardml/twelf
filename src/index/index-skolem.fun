(* Indexing (Constants and Skolem constants) *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor IndexSkolem (structure Global : GLOBAL
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

    (* Index array

       Invariant:
       For all type families  a
       indexArray (a) = c1,...,cn
       where c1,...,cn is a queue consisting of all constants with
       target family a
    *)
    val indexArray : (IntSyn.Head Queue.queue) Array.array =
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
    fun install fromCS (H as I.Const c) =
        (case (fromCS, I.sgnLookup (c))
          of (_, I.ConDec (_, _, _, _, A, I.Type)) => update (cidFromHead (I.targetHead A), H)
           | (I.Clause, I.ConDef (_, _, _, _, A, I.Type, _)) => update (cidFromHead (I.targetHead A), I.Def(c))
           | _ => ())
      | install fromCS (H as I.Skonst c) =
        (case I.sgnLookup (c)
           of I.SkoDec (_, _, _, A, I.Type) => update (cidFromHead (I.targetHead A), H)
            | _ => ())

    fun remove (a, cid) =
        (case Queue.deleteEnd (Array.sub (indexArray, a))
           of NONE => ()
            | SOME (I.Const cid', queue') =>
                if cid = cid' then Array.update (indexArray, a, queue')
                else ()
            | SOME (I.Skonst cid', queue') =>
                if cid = cid' then Array.update (indexArray, a, queue')
                else ())

    fun uninstall cid =
        (case I.sgnLookup cid
           of I.ConDec (_, _, _, _, A, I.Type) => remove (cidFromHead (I.targetHead A), cid)
            | I.SkoDec (_, _, _, A, I.Type) => remove (cidFromHead (I.targetHead A), cid)
            | _ => ())

    fun resetFrom mark =
        let
          val (limit, _) = I.sgnSize ()
          fun iter i = if i < mark then ()
                       else (uninstall i;
                             Array.update (indexArray, i, Queue.empty))
        in
          iter (limit - 1)
        end

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
    val resetFrom = resetFrom
    val install = install
    val lookup = lookup

  end (* local *)

end;  (* functor Index *)
