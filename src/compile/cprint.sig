(* Printer for Compiled Syntax *)
(* Author: Iliano Cervesato *)

signature CPRINT =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val goalToString: string -> IntSyn.dctx * CompSyn.Goal -> string
  val clauseToString: string -> IntSyn.dctx * CompSyn.ResGoal -> string
  val sProgToString: unit -> string
  val dProgToString: CompSyn.DProg -> string
  val subgoalsToString : string -> IntSyn.dctx * CompSyn.Conjunction -> string

end; (* signature CPRINT *)
