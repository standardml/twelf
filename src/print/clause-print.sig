(* Clause Printing *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature CLAUSEPRINT =
sig

  (*! structure IntSyn : INTSYN !*)
  structure Formatter : FORMATTER

  val formatClause : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  val formatConDec : IntSyn.ConDec -> Formatter.format

  val clauseToString : IntSyn.dctx * IntSyn.Exp -> string
  val conDecToString : IntSyn.ConDec -> string

  val printSgn : unit -> unit

end;  (* signature CLAUSEPRINT *)
