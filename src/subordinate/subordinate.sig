(* Subordination *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

signature SUBORDINATE =
sig
  (*! structure IntSyn : INTSYN !*)

  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit
  val installDef : IntSyn.cid -> unit
  val installFrozen : IntSyn.cid list -> unit

  val below : IntSyn.cid * IntSyn.cid -> bool (* transitive closure *)
  val belowEq : IntSyn.cid * IntSyn.cid -> bool	(* refl. transitive closure *)
  val equiv : IntSyn.cid * IntSyn.cid -> bool (* mutual dependency *)

  val respects : IntSyn.dctx * IntSyn.eclo -> unit (* respects current subordination? *)
  val respectsN : IntSyn.dctx * IntSyn.Exp -> unit (* respectsN(G, V), V in nf *)

  val checkNoDef : IntSyn.cid -> unit  (* not involved in type-level definition? *)

  val weaken : IntSyn.dctx * IntSyn.cid -> IntSyn.Sub

  val show : unit -> unit
end;  (* signature SUBORDINATE *)
