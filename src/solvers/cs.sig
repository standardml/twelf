(* Constraint Solver *)
signature CS =
sig
  (*! structure CSManager : CS_MANAGER !*)

  (* all a constraint solver must define is a structure
     suitable for the constraint solver manager to install.
  *)
  val solver : CSManager.solver

end  (* signature CS *)
