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


    (* nameState S = S'
     
       Invariant:
       If   |- S state     and S unnamed
       then |- S' State    and S' named
       and  |- S = S' state   
    *)
    fun nameState (S.State (n, (G, B), (IH, OH), d, O, H, R, F)) = 
        let 
	  val _ = Names.varReset ()
	  val G' = Names.ctxName G
	in
	  S.State (n, (G', B), (IH, OH), d, O, H, R, F)
	end

    (* format T = s'

       Invariant:
       If   T is a tag
       then s' is a string describing this tag in plain text 
    *)
    fun formatTag (S.Parameter) = Fmt.String "<p>"
      | formatTag (S.Lemma) = Fmt.String "<l>"
      | formatTag (S.Assumption k) = Fmt.String("<a" ^ Int.toString k ^ ">")
      | formatTag (S.Induction k) = Fmt.String ("<i" ^ Int.toString k ^ ">")


    (* formatCtx (G, B) = fmt'
     
       Invariant:
       If   |- G ctx       and G is already named
       and  |- B : G tags
       then fmt' is a format describing the context (G, B)
    *)
    fun formatCtx (I.Null, B) = []
      | formatCtx (I.Decl (I.Null, D), I.Decl (I.Null, T)) = 
          [formatTag T, Print.formatDec (I.Null, D)]
      | formatCtx (I.Decl (G, D), I.Decl (B, T)) =
	  formatCtx (G, B) @ [Fmt.String ",", Fmt.Space, Fmt.Break, formatTag T, 
			      Print.formatDec (G, D)]

    (* formatState S = fmt'
     
       Invariant:
       If   |- S state      and  S named
       then fmt' is a format describing the state S
    *)
    fun formatState (S.State (n, (G, B), (IH, OH), d, O, H, R, F)) = 
          Fmt.Vbox0 0 1 
	  [Fmt.HVbox0 1 0 1 (formatCtx (G, B)), Fmt.Break,
	   Fmt.String "------------------------", Fmt.Break,
	   FunPrint.formatForBare (G, F)]


    (* formatState S = S'
     
       Invariant:
       If   |- S state      and  S named
       then S' is a string descring state S in plain text
    *)
    fun stateToString S = 
      (Fmt.makestring_fmt (formatState S))


  in
    val nameState = nameState
    val formatState = formatState
    val stateToString = stateToString
  end (* local *)
end (* functor MTPrint *)