(* Tabled Abstract Machine      *)
(* Author: Brigitte Pientka     *)

signature TABLED =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.pskeleton -> unit) -> unit

  val updateGlobalTable : (CompSyn.Goal * bool) -> unit

  val keepTable : IntSyn.cid -> bool

  val fillTable : unit -> unit

  val nextStage : unit -> bool

  val reset : unit -> unit

  val tableSize : unit -> int

  val suspGoalNo : unit -> int

end;  (* signature TABLED *)

