(* Origins of Declarations *)
(* Author: Frank Pfenning *)

functor Origins (structure Global : GLOBAL
		 structure IntSyn' : INTSYN
		 structure Paths' : PATHS)
  : ORIGINS =
struct

  structure IntSyn = IntSyn'
  structure Paths = Paths'

  local
    val originArray = Array.array (Global.maxCid+1, ("", NONE))
        : (string * Paths.occConDec option) Array.array
  in
    fun installOrigin (cid, fileNameOpt) = Array.update (originArray, cid, fileNameOpt)
    fun originLookup (cid) = Array.sub (originArray, cid)
  end

end;  (* functor Origins *)
