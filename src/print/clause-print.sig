(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CLAUSEPRINT =
sig

  structure IntSyn : INTSYN
  structure Formatter : FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  val clauseToString : IntSyn.dctx * IntSyn.Exp -> string
  val theoremToString : IntSyn.cid -> string

end;  (* signature CLAUSEPRINT *)
