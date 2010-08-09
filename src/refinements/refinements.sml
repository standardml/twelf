structure Refinements :> REFINEMENTS =
  struct
    structure CidHashTable :> TABLE where type key = IntSyn.cid = IntHashTable

    exception Error of string

    (* namespace mapping names to refinement declarations -wjl 08-16-2009 *)
    val refinementNamespace : IntSyn.cid list CidHashTable.Table = CidHashTable.new (4096)
    val refinementInsert = CidHashTable.insert refinementNamespace
    val refinementLookup = CidHashTable.lookup refinementNamespace
    val refinementDelete = CidHashTable.delete refinementNamespace
    fun refinementClear () = CidHashTable.clear refinementNamespace

    fun addRefinement const_cid dec_cid =
        case refinementLookup const_cid
          of NONE => refinementInsert (const_cid, [dec_cid])
           | SOME cids => refinementInsert (const_cid, dec_cid :: cids)

    fun refinementDids cid =
        case refinementLookup cid
          of NONE => raise Error ("No refinements declared for constant `"
                                  ^ IntSyn.constName cid ^ "'")
           | SOME l => List.rev l
                       (* reverse the list so the decls appear
                        in the order they were declared *)

    fun refinements cid = List.map IntSyn.constType (refinementDids cid)

    fun refinedType cid =
        case IntSyn.sgnLookup cid
          of IntSyn.LFRSortDec (_, acid, _, _) => acid
           | _ => raise Error ("Not a sort: `" ^ IntSyn.constName cid ^ "'")

    fun reset () = refinementClear ()
  end
