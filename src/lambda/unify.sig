(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  structure IntSyn : INTSYN

  exception Unify of string
	
  val unify : IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)

  (* unifiable (Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.eclo * IntSyn.eclo -> bool

  val safeInvertExp : IntSyn.eclo * IntSyn.Sub -> IntSyn.Exp
  val safeInvertSub : IntSyn.Sub * IntSyn.Sub -> IntSyn.Sub

end;  (* signature UNIFY *)
