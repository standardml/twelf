(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

functor CPrint (structure IntSyn' : INTSYN
		structure CompSyn' : COMPSYN
		  sharing CompSyn'.IntSyn = IntSyn'
		structure Print: PRINT
		  sharing Print.IntSyn = IntSyn'
		structure Formatter : FORMATTER
		  sharing Print.Formatter = Formatter
		structure Names: NAMES
		  sharing Names.IntSyn = IntSyn')
  : CPRINT =
struct

  structure IntSyn = IntSyn'
  structure CompSyn = CompSyn'

  local
    open CompSyn
  in

    (* goalToString (G, g) where G |- g  goal *)
    fun goalToString (G, Atom(p)) =
	 "\tSOLVE  " ^ Print.expToString (G, p) ^ "\n"
      | goalToString (G, Impl (_,A,_,g)) =
	 "\tASSUME " ^ Print.expToString (G, A) ^ "\n" ^
	 goalToString (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), g) ^ "\n"
      | goalToString (G, All(D,g)) =
	 let
	   val D' = Names.decName (G, D)
	 in
	   "\tALL    " ^
	   Formatter.makestring_fmt (Print.formatDec (G, D')) ^ "\n" ^
	   goalToString (IntSyn.Decl (G, D'), g) ^ "\n"
	 end

    (* clauseToString (G, r) where G |- r  resgoal *)
    fun clauseToString (G, Eq(p)) =
	 "\tUNIFY  " ^ Print.expToString (G, p) ^ "\n"
      | clauseToString (G, And(r, A, g)) =
	 clauseToString (IntSyn.Decl(G, IntSyn.Dec(NONE, A)), r) ^
	 goalToString (G, g)
      | clauseToString (G, Exists(D, r)) =
	 let
	   val D' = Names.decName (G, D)
	 in
	   "\tEXISTS " ^
	   Print.decToString (G, D') ^ "\n" ^
	   clauseToString (IntSyn.Decl(G, D'), r)
	 end

    (* conDecToString (c, clause) printed representation of static clause *)
    fun conDecToString (c, SClause(r)) = 
	let
	  val _ = Names.varReset ()
	  val name = IntSyn.conDecName (IntSyn.sgnLookup c)
	  val l = String.size name
	in
	  name ^ (if l > 6 then ":\n" else ":") ^
	  clauseToString (IntSyn.Null, r) ^ "\n"
	end
      | conDecToString (c, Void) =
	  Print.conDecToString (IntSyn.sgnLookup c) ^ "\n\n"

    (* sProgToString () = printed representation of static program *)
    fun sProgToString () = 
	let val size = IntSyn.sgnSize ()
	    fun ts (cid) = if cid < size
			     then conDecToString (cid, CompSyn.sProgLookup cid)
				  ^ ts (cid+1)
			   else ""
	 in
	   ts 0
	 end

    (* dProgToString (G, dProg) = printed representation of dynamic program *)
    fun dProgToString (IntSyn.Null, IntSyn.Null) = ""
      | dProgToString (IntSyn.Decl(G,IntSyn.Dec(SOME x,_)),
		       IntSyn.Decl(dPool,SOME(r,_,_))) =
          dProgToString (G,dPool)
	  ^ "\nClause    " ^ x ^ ":\t"
	  ^ clauseToString (G, r)
      | dProgToString (IntSyn.Decl(G, IntSyn.Dec(SOME x,A)),
		       IntSyn.Decl(dPool, NONE)) =
	 dProgToString (G, dPool)
	 ^ "\nParameter " ^ x ^ ":\t"
	 ^ Print.expToString (G, A)

  end  (* local open ... *)

end; (* functor CPrint *)
