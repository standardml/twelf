(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

signature FUNPRINT =
sig
  structure FunSyn : FUNSYN
  structure Formatter : FORMATTER

  val formatFor : FunSyn.lfctx * FunSyn.For -> Formatter.format
  val formatPro : FunSyn.lfctx * FunSyn.mctx * FunSyn.Pro -> Formatter.format

  val forToString : FunSyn.lfctx * FunSyn.For -> string
  val proToString : FunSyn.lfctx * FunSyn.mctx * FunSyn.Pro  -> string

end;  (* signature PRINT *)

