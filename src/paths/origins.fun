(* Origins of Declarations *)
(* Author: Frank Pfenning *)

functor Origins
  (structure Global : GLOBAL
   structure Table : TABLE where type key = string
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Paths' : PATHS !*)
     )
  : ORIGINS =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)

  local
    val linesInfoTable : Paths.linesInfo Table.Table = Table.new (31)
    fun reset () = Table.clear linesInfoTable
    fun install (string, linesInfo) = Table.insert linesInfoTable (string, linesInfo)
    fun lookup (string) = Table.lookup linesInfoTable string
  in
    val reset = reset
    val installLinesInfo = install
    val linesInfoLookup = lookup
  end

  local
    structure CH = CidHashTable
    val originTable : (string * Paths.occConDec option) CH.Table = CH.new(1000)
  in
    val installOrigin = CH.insert originTable
    val originLookup = valOf o (CH.lookup originTable)
  end

end;  (* functor Origins *)
