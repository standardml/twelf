(* Trailing EVar Instantiations *)
(* Author: Carsten Schuermann *)

signature TRAIL =
sig

  structure IntSyn : INTSYN

  val reset       : unit -> unit
  val trail       : (unit -> 'a) -> 'a
  val instantiateEVar : IntSyn.Exp option ref * IntSyn.Exp -> unit

end; (* signature TRAIL *)
