(* Mode Table *)
(* Author: Frank Pfenning *)

signature MODETABLE =
sig

  exception Error of string

  val reset : unit -> unit

  (* single mode installation and lookup *)
  val installMode : (IntSyn.cid * ModeSyn.ModeSpine) -> unit 
  val modeLookup : IntSyn.cid -> ModeSyn.ModeSpine option
  val uninstallMode : IntSyn.cid -> bool (* true: was declared, false: not *)

  (* multiple mode installation and lookup *)
  val installMmode : (IntSyn.cid * ModeSyn.ModeSpine) -> unit 
  val mmodeLookup : IntSyn.cid -> ModeSyn.ModeSpine list

end;  (* signature MODETABLE *)
