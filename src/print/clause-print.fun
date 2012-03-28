(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* This is like printing of expressions, except that
   types are interpreted as programs and therefore
   printed with backward arrows `<-'
*)

functor ClausePrint
  ((*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Formatter' : FORMATTER
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
     sharing Print.Formatter = Formatter'
   structure Symbol : SYMBOL)
     : CLAUSEPRINT =
struct

  (*! structure IntSyn = IntSyn' !*)
structure Formatter = Formatter'

local
  (* some shorthands *)
  structure I = IntSyn
  structure F = Formatter
  val Str = F.String
  fun Str0 (s, n) = F.String0 n s
  fun sym (s) = Str0 (Symbol.sym s)

  fun parens (fmt) = F.Hbox [sym "(", fmt, sym ")"]

  (* assumes NF *)
  fun fmtDQuants (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
      let
        val D' = Names.decEName (G, D)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
      end
    | fmtDQuants (G, I.Pi ((D as I.Dec (_, V1), I.Meta), V2)) =
      let
        val D' = Names.decEName (G, D)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtDQuants (I.Decl (G, D'), V2)
      end
    | fmtDQuants (G, V as I.Pi _) = (* P = I.No *)
        [F.HOVbox (fmtDSubGoals (G, V, nil))]
    | fmtDQuants (G, V) = (* V = Root _ *)
        [Print.formatExp (G, V)]
  and fmtDSubGoals (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), acc) =
        fmtDSubGoals (I.Decl (G, D), V2,
                      F.Break :: sym "<-" :: F.Space :: fmtGparens (G, V1)
                      :: acc)
    | fmtDSubGoals (G, V as I.Pi _, acc) = (* acc <> nil *)
        parens (F.HVbox (fmtDQuants (G, V))) :: acc
    | fmtDSubGoals (G, V, acc) = (* V = Root _ *)
        Print.formatExp (G, V) :: acc
  and fmtDparens (G, V as I.Pi _) = parens (F.HVbox (fmtDQuants (G, V)))
    | fmtDparens (G, V) = (* V = Root _ *)
        Print.formatExp (G, V)
  and fmtGparens (G, V as I.Pi _) = parens (F.HVbox (fmtGQuants (G, V)))
    | fmtGparens (G, V) = (* V = Root _ *)
        Print.formatExp (G, V)
  and fmtGQuants (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2)) =
      let
        val D' = Names.decLUName (G, D)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
      end
    | fmtGQuants (G, I.Pi ((D as I.Dec (_, V1), I.Meta), V2)) =
      let
        val D' = Names.decLUName (G, D)
      in
        sym "{" :: Print.formatDec (G, D') :: sym "}" :: F.Break
        :: fmtGQuants (I.Decl (G, D'), V2)
      end
    | fmtGQuants (G, V) = (* P = I.No or V = Root _ *)
        [F.HOVbox (fmtGHyps (G, V))]
  and fmtGHyps (G, I.Pi ((D as I.Dec (_, V1), I.No), V2)) =
        fmtDparens (G, V1) :: F.Break :: sym "->" :: F.Space :: fmtGHyps (I.Decl (G, D), V2)
    | fmtGHyps (G, V as I.Pi _) = (* P = I.Maybe *)
        [F.HVbox (fmtGQuants (G, V))]
    | fmtGHyps (G, V) = (* V = Root _ *)
        [Print.formatExp (G, V)]

  fun fmtClause (G, V) = F.HVbox (fmtDQuants (G, V))

  fun fmtClauseI (0, G, V) = fmtClause (G, V)
    | fmtClauseI (i, G, I.Pi ((D, _), V)) =
        fmtClauseI (i-1, I.Decl (G, Names.decEName (G, D)), V)

  fun fmtConDec (I.ConDec (id, parent, i, _, V, I.Type)) =
      let
        val _ = Names.varReset IntSyn.Null
        val Vfmt = fmtClauseI (i, I.Null, V)
      in
        F.HVbox [Str0 (Symbol.const (id)), F.Space, sym ":", F.Break,
                 Vfmt, sym "."]
      end
    | fmtConDec (condec) =
      (* type family declaration, definition, or Skolem constant *)
      Print.formatConDec (condec)

in

  fun formatClause (G, V) = fmtClause (G, V)
  fun formatConDec (condec) = fmtConDec (condec)

  fun clauseToString (G, V) = F.makestring_fmt (formatClause (G, V))
  fun conDecToString (condec) = F.makestring_fmt (formatConDec (condec))

  fun printSgn () =
      IntSyn.sgnApp (fn (cid) => (print (conDecToString (IntSyn.sgnLookup cid)); print "\n"))
end  (* local ... *)

end  (* functor ClausePrint *)
