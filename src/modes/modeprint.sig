(* Printing Mode Declarations *)
(* Author: Carsten Schuermann *)

signature MODEPRINT =
sig
  (*! structure ModeSyn : MODESYN !*)

  val modeToString : IntSyn.cid * ModeSyn.ModeSpine -> string
  val modesToString : (IntSyn.cid * ModeSyn.ModeSpine) list -> string
end;  (* signature MODEPRINT *)
