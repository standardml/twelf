(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

signature TABLED =
sig

  structure IntSyn  : INTSYN
  structure CompSyn : COMPSYN
  structure Unify : UNIFY 


  val SuspGoals : ((((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg * (IntSyn.Exp  -> unit)) * 
		    Unify.unifTrail) list) ref 

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (IntSyn.Exp -> unit) -> unit

  val nextStage : unit -> bool

  val reset : unit -> unit

end;  (* signature TABLED *)

