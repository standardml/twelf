(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature COMPILE =
sig
  exception Error of string

  val optimize : bool ref

  val install : IntSyn.ConDecForm -> IntSyn.cid -> unit

  val compileClause: bool -> (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp)
                          -> CompSyn.ResGoal
  val compileCtx: bool -> (IntSyn.Dec IntSyn.Ctx) -> CompSyn.DProg
  val compileGoal: (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) -> CompSyn.Goal

  (* for the meta theorem prover  --cs *)
  val compilePsi: bool -> (Tomega.Dec IntSyn.Ctx) -> CompSyn.DProg
 
end; (* signature COMPILE *)
