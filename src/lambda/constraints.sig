(* Manipulating Constraints *)
(* Author: Jeff Polakow, Frank Pfenning *)

signature CONSTRAINTS =
sig

   structure IntSyn : INTSYN

   exception Error of IntSyn.Eqn list

   val simplify : IntSyn.Eqn list -> IntSyn.Eqn list
   val warnConstraints : IntSyn.name list -> unit

end;  (* signature CONSTRAINTS *)
