(* Subordination *)
(* Author: Carsten Schuermann *)

signature SUBORDINATE =
sig
  structure IntSyn : INTSYN
    
  val reset : unit -> unit
  val install : IntSyn.cid -> unit

  val below : IntSyn.cid * IntSyn.cid -> bool (* transitive closure *)
  val belowEq : IntSyn.cid * IntSyn.cid -> bool	(* refl. transitive closure *)
  val equiv : IntSyn.cid * IntSyn.cid -> bool (* mutual dependency *)
end;  (* signature SUBORDINATE *)
