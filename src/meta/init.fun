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
	fun init' ((G, B), S.All (_, O), (F.All (F.Prim D, F'), s), Ss) = 
              init' ((I.Decl (G, N.decName (G, Whnf.normalizeDec (D, s))), 
		     I.Decl (B, S.Assumption (!MTPGlobal.maxSplit))), 
		     O, (F', I.dot1 s), Ss)
	      (* it is possible to calculuate 
	         index/induction variable information here 
		 define occursOrder in StateSyn.fun  --cs *)
   (*      | init' (G, B, O, (F.All (F.Block _, F), s)) =
	   no such case yet  --cs *)
	  | init' (GB, O, (F.And (F1', F2'), s), Ss) = 
	      init' (GB, O, (F1', s), init' (GB, O, (F2', s), Ss))
	  | init' (GB, O, (F.TClo (F', s'), s), Ss) =
	      init' (GB, O, (F', I.comp (s', s)), Ss)
	  | init' (GB, O, Fs as (F.Ex (D, F'), s), Ss) = 
	      S.State (List.length Ss + 1, GB, (F, OF), 1, O, nil, nil, F.TClo Fs) :: Ss
      in
	(N.varReset ();
	 init' ((I.Null, I.Null), OF, (F, I.id), nil))
      end

  in
    val init = init
  end (* local *)
end; (* functor Init *)
