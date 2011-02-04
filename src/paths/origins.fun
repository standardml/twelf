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

    val linesInfoTable : Paths.linesInfo Table.Table = Table.new (31)
    fun installLinesInfo (string, linesInfo) = Table.insert linesInfoTable (string, linesInfo)
    fun linesInfoLookup (string) = Table.lookup linesInfoTable string

    structure CH = CidHashTable
    val originTable : (string * Paths.occConDec option) CH.Table = CH.new(1000)
    val installOrigin = CH.insert originTable
    val originLookup = valOf o (CH.lookup originTable)

    structure MH = MidHashTable
    val mOriginTable : (string * Paths.region) MH.Table = MH.new(100)
    val installMOrigin = MH.insert mOriginTable
    val mOriginLookup = valOf o (MH.lookup mOriginTable)

    fun reset () = (Table.clear linesInfoTable; CH.clear originTable; MH.clear mOriginTable)

end;  (* functor Origins *)
