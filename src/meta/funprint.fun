(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

functor FunPrint (structure FunSyn' : FUNSYN
		  structure Formatter : FORMATTER
		  structure Print : PRINT
		    sharing Print.Formatter = Formatter
		    sharing Print.IntSyn = FunSyn'.IntSyn) 
  : FUNPRINT =
struct
  structure FunSyn = FunSyn'
  structure Formatter = Formatter

  local
    structure F = FunSyn
    structure I = FunSyn.IntSyn
    structure Fmt = Formatter
    structure P = Print


    (* formatCtxBlock (G, (G1, s1)) = (G', s', fmts')
 
       Invariant:
       If   |- G ctx
       and  G |- G1 ctx
       and  G2 |- s1 : G 
       then G' = G2, G1 [s1]
       and  G' |- s' : G, G1 
       and  fmts is a format list of G1[s1]
    *)

    fun formatCtxBlock (G, (I.Null, s)) = (G, s, nil)
      | formatCtxBlock (G, (I.Decl (G', D), s)) =
          let 
	    val (G'', s'', fmts) = formatCtxBlock (G, (G', s))
	    val D'' = I.decSub (D, s'')
	    val fmt = P.formatDec (G'', D'')
	  in
	    (I.Decl (G'', D''), I.dot1 s'', fmts @ [Fmt.String",", 
						    Fmt.Break,
						    fmt])
	  end


    fun formatFor' (G, (F.All (LD, F), s)) = 
        (case LD 
	  of F.Prim D => Fmt.HVbox [Fmt.String "{{", P.formatDec 
				    (G, I.decSub (D, s)), 
				    Fmt.String "}}", Fmt.Break,
		  formatFor' (I.Decl (G, D), (F, I.dot1 s))]
           | F.Block (F.CtxBlock (l, G')) => 
	     let
	       val (G'', s'', fmts) = formatCtxBlock (G, (G', s))
	     in
	       Fmt.HVbox [Fmt.String "{", 
			  Fmt.Hbox fmts, 
			  Fmt.String "}", Fmt.Break,
			  formatFor' (G'', (F, s''))]
	     end)
      | formatFor' (G, (F.Ex (D, F), s)) =
	  Fmt.HVbox [Fmt.String "[[", P.formatDec 
		     (G, I.decSub (D, s)), Fmt.String "]]", Fmt.Break,
		    formatFor' (I.Decl (G, D), (F, I.dot1 s))]
      | formatFor' (G, (F.And (F1, F2), s)) =
	  Fmt.HVbox [formatFor' (G, (F1, s)), Fmt.Break, Fmt.String "^", Fmt.Break,
		    formatFor' (G, (F2, s))]
      | formatFor' (G, (F.True, s)) = 
	  Fmt.String "True"
      | formatFor' (G, (F.TClo (F, s), s')) = 
          formatFor' (G, (F, I.comp (s, s')))
	  
    fun formatFor (Psi, F) = formatFor' (F.makectx Psi, (F, I.id))

    fun formatPro (Psi, Delta, F) = Fmt.String "Not yet implemented"  

    fun forToString Args = Fmt.makestring_fmt (formatFor Args)
    fun proToString Args = Fmt.makestring_fmt (formatPro Args)

  in
    val formatFor = formatFor
    val formatPro = formatPro
      
    val forToString = forToString
    val proToString = proToString 

  end
end;  (* signature FUNPRINT *)

