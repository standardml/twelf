(* Extensible operation on foreign matter *)
(* Author: Aleksey Kliger *)

functor FgnOpnTable (type arg ; type result) :>
        FGN_OPN where type arg = arg
                where type result = result = struct
  type csid = int
  type rep = exn
  type arg = arg
  type result = result
  type func = (rep -> arg -> result)

  type table = func array

  fun initializeTable tbl = let
    exception CSfunNotInstalled of csid
    val maxCSid = (*Global.maxCSid*) 50
    fun unimplemented csid = fn _ => raise (CSfunNotInstalled csid)
  in
      Array.tabulate (maxCSid +1 , unimplemented)
  end

  val table : table = initializeTable ()

  fun install (csid, f) = Array.update (table, csid, f)

  fun apply (csid, rep) = Array.sub (table, csid) rep


end