(* Abstract Machine *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

signature ABSMACHINESBT =
sig

  (*! structure IntSyn  : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)

  val solve     : (CompSyn.Goal * IntSyn.Sub) * CompSyn.DProg
                  * (CompSyn.Flatterm list -> unit) -> unit 


end;  (* signature ABSMACHINESBT *)
