(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

signature ABSMACHINE =
sig

  structure IntSyn  : INTSYN
  structure CompSyn : COMPSYN

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.dprog
                  * (IntSyn.Exp -> unit) -> unit

  val rSolve    : IntSyn.eclo * (CompSyn.ResGoal * IntSyn.Sub)
                  * CompSyn.dprog * (IntSyn.Spine -> unit) -> unit

  val matchAtom : IntSyn.eclo * CompSyn.dprog
                  * (IntSyn.Exp -> unit) -> unit

end;  (* signature ABSMACHINE *)
