(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

signature MODEPRINT =
sig
  structure ModeSyn : MODESYN

  val modeToString : ModeSyn.IntSyn.cid * ModeSyn.ModeSpine -> string
end;  (* signature MODEPRINT *)
