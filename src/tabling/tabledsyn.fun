(* Tabled Syntax *)
(* Author: Brigitte Pientka *)

functor TabledSyn ((*! structure IntSyn' : INTSYN !*)
                 structure Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn' !*)
                 structure Table : TABLE where type key = int
                 structure Index : INDEX
                 (*! sharing Index.IntSyn = IntSyn' !*)
                     ) : TABLEDSYN =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  datatype Tabled = yes | no

(*  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * string option
  *)
  local
    structure I = IntSyn

    val tabledSignature : bool Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets tabled array
    *)

    fun reset () = Table.clear tabledSignature

    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)
    fun installTabled a = Table.insert tabledSignature (a, false)

    (* installTabled (a, tabled) = ()

       Effect: the tabled is stored with the type family a
    *)

    fun installKeepTable a =
      ((* Table.delete tabledSignature a; *)
       Table.insertShadow tabledSignature (a, true);())


    (* tablingLookup a = bool

       Looks up whether the predicat a is tabled

    *)

    fun tabledLookup a =
     (case (Table.lookup tabledSignature a) of
       NONE => false
     | SOME _ => true)


    (* keepTable a = bool

       if we should keep the table for this predicate a
        then returns true
          otherwise false
    *)

    fun keepTable a =
     (case (Table.lookup tabledSignature a) of
       NONE => false
     | SOME true => true
     | SOME false => false)

  in
    val reset = reset
    val installTabled = installTabled
    val installKeepTable =  installKeepTable
    val tabledLookup = tabledLookup
    val keepTable = keepTable
  end
end;  (* functor TabledSyn *)
