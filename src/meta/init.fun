(* Initialization *)
(* Author: Carsten Schuermann *)

functor MTPInit (structure MTPGlobal : MTPGLOBAL
		  structure IntSyn : INTSYN
		  structure Names : NAMES
		    sharing Names.IntSyn = IntSyn
                  structure FunSyn' : FUNSYN
		    sharing FunSyn'.IntSyn = IntSyn
		  structure StateSyn' : STATESYN
		    sharing StateSyn'.FunSyn = FunSyn'
		  structure Formatter : FORMATTER
		  structure Whnf : WHNF
		    sharing Whnf.IntSyn = IntSyn
		  structure Print : PRINT
		    sharing Print.Formatter = Formatter
		    sharing Print.IntSyn = IntSyn
		  structure FunPrint : FUNPRINT
		    sharing FunPrint.FunSyn = FunSyn'
		    sharing FunPrint.Formatter = Formatter)
  : MTPINIT =
struct
  structure FunSyn = FunSyn'
  structure StateSyn = StateSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure N = Names
    structure F = FunSyn
    structure S = StateSyn 
    structure Fmt = Formatter
      
    fun init (F, OF) = 
      let 
	fun init' ((G, B), S.All (_, O), (F.All (F.Prim D, F), s)) = 
              init' ((I.Decl (G, N.decName (G, Whnf.normalizeDec (D, s))), 
		     I.Decl (B, S.Assumption (!MTPGlobal.maxSplit))), 
		     O, (F, I.dot1 s))
	  (*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
	   no such case ye
sharing StateSyn.Order = Ordert  --cs *)
	  | init' (GB, O, (F.TClo (F, s'), s)) =
	      init' (GB, O, (F, I.comp (s', s)))
	  | init' (GB, O, Fs as (F.Ex (D, F), s)) = 
	      [S.State (GB, (F, OF), 1, O, nil, F. TClo Fs)]
      in
	(N.varReset ();
	 init' ((I.Null, I.Null), OF, (F, I.id)))
      end

  in
    val init = init
  end (* local *)
end; (* functor Init *)
