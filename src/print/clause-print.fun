(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)

functor ClausePrint
  (structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Formatter' : FORMATTER
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'
     sharing Print.Formatter = Formatter')
     : CLAUSEPRINT =
struct

structure IntSyn = IntSyn'
structure Formatter = Formatter'

local
  (* some shorthands *)
  structure I = IntSyn
  structure F = Formatter
  val Str = F.String

  (* parens for ({x:A} B) or (A -> B) only *)
  (* arg must be in whnf *)
  fun parens (G, Vs as (I.Pi _, s)) = F.Hbox [Str "(", Print.formatExp (G, I.EClo Vs), Str ")"]
    | parens (G, Vs) = Print.formatExp (G, I.EClo Vs)

  (* assume NF? *)
  fun fmtClause (G, (V,s), acc) = fmtClauseW (G, Whnf.whnf (V,s), acc)

  and fmtClauseW (G, (I.Pi ((D as I.Dec (_, V1), I.No), V2), s), acc) =
        fmtClause (I.Decl (G, D), (* I.decSub (D, s) *)
		   (V2, I.dot1 s),
		   F.Break
		   :: Str "<-" :: F.Space :: parens (G, Whnf.whnf (V1,s))
		   :: acc)
    | fmtClauseW (G, (I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), s), nil) =
      let
	val D' = Names.decName (G, D)
      in
	Str "{" :: Print.formatDec (G, D') :: Str "}" :: F.Break
	:: fmtClause (I.Decl (G, D'),  (* I.decSub (D', s) *)
		      (V2, I.dot1 s),
		      nil)
      end
    | fmtClauseW (G, (V, s), acc) =
      Print.formatExp (G, I.EClo (V, s)) :: acc


  (* theoremToString a = s'
   
     Invariant: 
     If   Sigma (a) = V
     then s' is a string of V (where implicit parameters are omitted)
   *)

  fun theoremToString a = 
      let 
        val V = I.constType a
	val imp = I.constImp a

	fun print' (G, V', 0) = Print.expToString (G, V')
	  | print' (G, I.Pi ((D, _), V'), n) =
	      print' (I.Decl (G, Names.decName (G, D)), V', n-1)
      in
	print' (I.Null, V, imp)
      end


in

  fun formatClause (G, V) = F.Vbox (fmtClause (G, (V, I.id), nil))
  fun clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
  val theoremToString = theoremToString

end  (* local ... *)

end  (* functor ClausePrint *)
