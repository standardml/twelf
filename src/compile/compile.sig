(* Compiler *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature COMPILE =
sig

  (*! structure IntSyn: INTSYN !*)
  (*! structure CompSyn: COMPSYN !*)


  exception Error of string

  datatype Opt = datatype CompSyn.Opt

  val optimize : Opt ref

  val install : IntSyn.ConDecForm -> IntSyn.cid -> unit

  val sProgReset : unit -> unit


  val compileCtx: bool -> (IntSyn.Dec IntSyn.Ctx) -> CompSyn.DProg  

  val compileGoal: (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) -> CompSyn.Goal

  (* for the meta theorem prover  --cs *)
  val compilePsi: bool -> (Tomega.Dec IntSyn.Ctx) -> CompSyn.DProg
 

end; (* signature COMPILE *)
