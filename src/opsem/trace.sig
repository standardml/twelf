signature TRACE =
sig

  (* Program interface *)
  structure IntSyn : INTSYN

  type goalTag
  val tagGoal : unit -> goalTag

  datatype Event =
    AtomGoal of unit -> IntSyn.dctx * IntSyn.Exp
  | ImplGoal of unit -> IntSyn.dctx * IntSyn.Exp
  | AllGoal of unit -> IntSyn.dctx * IntSyn.Exp

  | IntroHyp of unit -> IntSyn.dctx * IntSyn.Dec
  | DischargeHyp of unit -> IntSyn.dctx * IntSyn.Dec

  | IntroParm of unit -> IntSyn.dctx * IntSyn.Dec
  | DischargeParm of unit -> IntSyn.dctx * IntSyn.Dec

  | Unify of unit -> IntSyn.Eqn (* goal == clause head *)
  | Resolved of IntSyn.dctx * IntSyn.Head (* resolved with clause H *)
  | Subgoal of IntSyn.dctx * IntSyn.Head * (unit -> int) (* nth subgoal of H : _ *)
  | IntroEVar of unit -> IntSyn.dctx * IntSyn.Exp * IntSyn.Exp (* X : V *)

  | SolveGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)
  | RetryGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)
  | FailGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)

  | TryClause of unit -> IntSyn.dctx * IntSyn.Head
  | FailClauseShallow of unit -> IntSyn.dctx * IntSyn.Head
  | FailClauseDeep of unit -> IntSyn.dctx * IntSyn.Head 

  val signal : Event -> unit
  val init : unit -> unit		(* initialize trace, break and tag *)

  (* User interface *)
  datatype 'a Spec =
    None
  | Some of 'a list
  | All

  val trace : string Spec -> unit
  val break : string Spec -> unit

  val status : unit -> unit
  val reset : unit -> unit		(* remove all tracing and breakpoints *)

end;  (* signature TRACE *)
