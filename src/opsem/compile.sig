(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature COMPILE =
sig

  structure IntSyn: INTSYN
  structure CompSyn: COMPSYN

  val install : IntSyn.cid -> unit

  val compileClause: IntSyn.Exp -> CompSyn.ResGoal
  val compileCtx: IntSyn.Dec IntSyn.Ctx -> CompSyn.dprog
  val compileGoal: IntSyn.Exp -> CompSyn.Goal

end; (* signature COMPILE *)
