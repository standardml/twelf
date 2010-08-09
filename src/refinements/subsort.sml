structure Subsort :> SUBSORT =
  struct
    exception Error of string

    val table : IntSet.intset IntHashTable.Table = IntHashTable.new 10

    fun union (set1, set2) = IntSet.foldl IntSet.insert set1 set2

    fun insert (cid, v) =
        case IntHashTable.insertShadow table (cid, v) of
            NONE => ()
          | SOME _ => raise Error ("already in subsort table: "
                                   ^ IntSyn.constName cid ^ " (bug?)")

    fun update (k, v) = IntHashTable.insert table (k, v)

    fun supersorts cid =
        case (IntHashTable.lookup table cid) of
             NONE => raise Error ("not in subsort table: "
                                  ^ IntSyn.constName cid ^ " (bug?)")
           | SOME v => v

    fun clear () = IntHashTable.clear table

    fun singleton cid = IntSet.insert (cid, IntSet.empty)

    (* ensure reflexivity when we add a new sort *)
    fun addSort cid = insert (cid, singleton cid)

    (* ensure transitivity when we add a new edge *)
    (* for every cid:
        if supersorts(cid) include cid1, add supersorts(cid2) *)
        (* but what if cid2 has yet to have some extra supersorts added to it?
           do you have to iterate to fixed point or something? *)
        (* possibly it can't have any extra supersorts added to it?  other than
           itself, which it already has? *)
    fun addSubsort cid1 cid2 =
        let val supers2 = supersorts cid2
        in
            IntHashTable.app
                (fn (cid, supers) =>
                    if IntSet.member (cid1, supers)
                    then update (cid, union (supers, supers2))
                    else ())
                table
        end

    fun subsort cid1 cid2 = IntSet.member (cid2, supersorts cid1)
    (*
        (print ("*** Checking: " ^ IntSyn.constName cid1
                        ^ " <: " ^ IntSyn.constName cid2 ^ " ... ");
         if IntSet.member (cid2, supersorts cid1) then
            (print "true!\n"; true)
        else
            (print "false!\n"; false))
    *)

    fun intSetToString set =
        let val lst = IntSet.foldl (op ::) [] set
        in
            String.concatWith ", " (List.map Int.toString lst)
        end

    fun printSubsorts () =
        IntHashTable.app
            (fn (cid, set) =>
                (print (Int.toString cid ^ ": " ^ intSetToString set ^ "\n")))
            table
  end
