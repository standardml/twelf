(* Printing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

signature PRINT =
sig
  structure IntSyn : INTSYN
  structure Formatter : FORMATTER

  val implicit : bool ref
  val printDepth : int option ref
  val printLength : int option ref

  val formatDec : IntSyn.dctx * IntSyn.Dec -> Formatter.format
  val formatExp : IntSyn.dctx * IntSyn.Exp -> Formatter.format
  val formatSpine : IntSyn.dctx * IntSyn.Spine -> Formatter.format list
  val formatConDec : IntSyn.ConDec -> Formatter.format
  val formatConDecI : IntSyn.ConDec -> Formatter.format
  val formatEqn : IntSyn.Eqn -> Formatter.format

  val decToString : IntSyn.dctx * IntSyn.Dec -> string
  val expToString : IntSyn.dctx * IntSyn.Exp -> string
  val conDecToString : IntSyn.ConDec -> string
  val eqnToString : IntSyn.Eqn -> string
  val eqnsToString : IntSyn.Eqn list -> string (* assigns names in contexts *)

  val evarInstToString : (IntSyn.Exp * IntSyn.name) list -> string
  val evarConstrToStringOpt : (IntSyn.Exp * IntSyn.name) list -> string option

  val printSgn : unit -> unit

end;  (* signature PRINT *)
