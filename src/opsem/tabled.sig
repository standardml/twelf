(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

signature TABLED =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  structure Unify : UNIFY 


  val SuspGoals : ((((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (CompSyn.pskeleton -> unit)) * 
		    Unify.unifTrail * int ref) list) ref 

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.pskeleton -> unit) -> unit

  val nextStage : unit -> bool

  val reset : unit -> unit

  val solExists : (IntSyn.Exp * IntSyn.Sub) -> bool


end;  (* signature TABLED *)

