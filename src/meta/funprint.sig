(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

signature FUNPRINT =
sig
  (*! structure FunSyn : FUNSYN !*)
  structure Formatter : FORMATTER

  val formatForBare : IntSyn.dctx * FunSyn.For -> Formatter.format
  val formatFor : FunSyn.lfctx * FunSyn.For -> string list -> Formatter.format
  val formatPro : FunSyn.lfctx * FunSyn.Pro -> string list -> Formatter.format
  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format

  val forToString : FunSyn.lfctx * FunSyn.For -> string list -> string
  val proToString : FunSyn.lfctx * FunSyn.Pro -> string list -> string
  val lemmaDecToString : FunSyn.LemmaDec -> string
end;  (* signature PRINT *)

