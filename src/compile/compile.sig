(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature COMPILE =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  exception Error of string

  val optimize : bool ref

  val install : IntSyn.ConDecForm -> IntSyn.cid -> unit

  val compileClause: bool -> (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp)
                          -> CompSyn.ResGoal
  val compileCtx: bool -> (IntSyn.Dec IntSyn.Ctx) -> CompSyn.DProg
  val compileGoal: (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) -> CompSyn.Goal

end; (* signature COMPILE *)
