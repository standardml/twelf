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
    val originArray = Array.array (Global.maxCid+1, ("", NONE))
        : (string * Paths.occConDec option) Array.array
  in
    fun installOrigin (cid, fileNameOpt) = Array.update (originArray, cid, fileNameOpt)
    fun originLookup (cid) = Array.sub (originArray, cid)
  end

end;  (* functor Origins *)
