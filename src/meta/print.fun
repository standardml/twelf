(* Meta Printer Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTPrint (structure IntSyn : INTSYN
		 structure FunSyn : FUNSYN
		   sharing FunSyn.IntSyn = IntSyn
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn
		 structure StateSyn' : STATESYN
		   sharing StateSyn'.FunSyn = FunSyn
		 structure Formatter' : FORMATTER
		 structure Print : PRINT
		   sharing Print.Formatter = Formatter'
		   sharing Print.IntSyn = IntSyn
		 structure FunPrint : FUNPRINT
		   sharing FunPrint.FunSyn = FunSyn
		   sharing FunPrint.Formatter = Formatter')
  : MTPRINT =
struct
  structure Formatter = Formatter'
  structure StateSyn = StateSyn'

  exception Error of string 

  local
    structure I = IntSyn
    structure N = Names
    structure S = StateSyn 
    structure Fmt = Formatter

    fun formatCtx (I.Null) = (I.Null, [])
      | formatCtx (I.Decl (I.Null, D)) = 
        let 
	  val D' = Names.decName (I.Null, D)
	in
          (I.Decl (I.Null, D'), 
	   [Print.formatDec (I.Null, D')])
	end
      | formatCtx (I.Decl (G, D)) =
	  let 
	    val (G', fmt) = formatCtx G
	    val D' = Names.decName (G', D)
	  in
	    (I.Decl (G', D'), 
	      fmt @ [Fmt.String ",", Fmt.Space, Fmt.Break,
			   Print.formatDec (G', D')])
	  end

    fun formatState (S.State ((G, B), (IH, OH), d, O, H, F)) = 
        let 
	  val (G', fmt) = formatCtx G
	in
          Fmt.Vbox0 0 1 
	  [Fmt.HVbox0 1 0 1 fmt, Fmt.Break,
	   Fmt.String "------------------------", Fmt.Break,
	   FunPrint.formatForBare (G', F)]
	end

    fun stateToString  (S) = 
      (Names.varReset ();
       Fmt.makestring_fmt (formatState S))


  in
    val formatState = formatState
    val stateToString = stateToString
  end (* local *)
end (* functor MTPrint *)