signature TRACE =
sig

  (* Program interface *)
  structure IntSyn : INTSYN

  type goalTag
  val tagGoal : unit -> goalTag

  datatype Event =
    AtomGoal of IntSyn.Exp
  | ImplGoal of IntSyn.Exp
  | AllGoal of IntSyn.Exp

  | IntroHyp of IntSyn.Head * IntSyn.Dec
  | DischargeHyp of IntSyn.Head * IntSyn.Dec

  | IntroParm of IntSyn.Head * IntSyn.Dec
  | DischargeParm of IntSyn.Head * IntSyn.Dec

  | Unify of IntSyn.Exp * IntSyn.Exp	(* goal == clause head *)
  | Resolved of IntSyn.Head * IntSyn.Head (* resolved with clause c, fam a *)
  | Subgoal of (IntSyn.Head * IntSyn.Head) * (unit -> int) (* clause c, fam a, nth subgoal *)
  | IntroEVar of IntSyn.Exp

  | SolveGoal of goalTag * IntSyn.Head * IntSyn.Exp
  | RetryGoal of goalTag * IntSyn.Head * IntSyn.Exp
  | FailGoal of goalTag * IntSyn.Head * IntSyn.Exp

  | TryClause of IntSyn.Head
  | FailClauseShallow of IntSyn.Head
  | FailClauseDeep of IntSyn.Head 

  val signal : IntSyn.dctx * Event -> unit
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
