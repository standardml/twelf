(* World Printer *)
(* Author: Carsten Schuermann *)

functor WorldPrint (structure Global : GLOBAL
		    structure WorldSyn' : WORLDSYN
		    (*! sharing WorldSyn'.IntSyn = IntSyn !*)
		    structure Names : NAMES
		    (*! sharing Names.IntSyn = IntSyn !*)
		    structure Formatter' : FORMATTER
		    structure Print : PRINT
		      sharing Print.Formatter = Formatter'
		      (*! sharing Print.IntSyn = IntSyn !*)
			)
  : WORLDPRINT =

struct
  structure Formatter = Formatter'
  structure Tomega = Tomega

  exception Error of string 

  local
    structure I = IntSyn
    structure T = Tomega
    structure N = Names
    structure W = WorldSyn'
    structure Fmt = Formatter
      

    (* formatdlist (G, L) k = LF
      
       Invariant:
       LF is the resulting list of formats
    *)
    (*
    fun formatdlist (G, nil) k = (k (G, nil) )
      | formatdlist (G, D :: L) k = 
          (formatdlist (I.Decl (G, D), L) 
	   (fn (G', F) => k (G', Fmt.Break :: 
			     Fmt.String "{" :: Print.formatDec (G, D) ::
			     Fmt.String "}" :: F)))
  
    fun separator (W.Closed, F) = F
      | separator (_, F) = Fmt.Break :: Fmt.String "| " :: F

    fun formatWorld (W.Closed, F) = Fmt.HVbox (Fmt.String "(" :: F)
      | formatWorld (W.Schema (W, W.LabelDec (_, L1, L2)), F) =
          formatWorld (W, separator (W, Fmt.HVbox
	    (formatdlist (I.Null, L1) 
	     (fn (G', F') => formatdlist (G', L2)
	      (fn (G'', F'') =>
	       (case F' 
		 of nil => [Fmt.String "pi", Fmt.HVbox F'', Fmt.String ""]
		  | _ => [Fmt.String "some", Fmt.HVbox F', Fmt.Break, 
		Fmt.String "pi", Fmt.HVbox F'', Fmt.String ""]))))
		       :: F))
    fun worldToString W = Fmt.makestring_fmt (formatWorld (W, [Fmt.String ")"]))
    *)
    (* This is incorrect.  FIX!!! *)
    fun cidToFmt (cid) = Fmt.String (Names.qidToString (Names.constQid cid))
    fun formatCids (nil) = nil
      | formatCids (cid::nil) = [cidToFmt cid]
      | formatCids (cid::cids) = cidToFmt cid
                                 :: Fmt.Break :: Fmt.String "|" :: Fmt.Space
                                 :: formatCids cids

    fun formatWorlds (T.Worlds cids) =
        Fmt.Hbox [Fmt.String "(", Fmt.HVbox (formatCids cids), Fmt.String ")"]
    

    fun worldsToString (W) = Fmt.makestring_fmt (formatWorlds W)

  in
    val formatWorlds = formatWorlds
    val worldsToString = worldsToString
  end
end;
