(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  structure IntSyn : INTSYN

  exception Unify of string
	
  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)

  (* unifiable (Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

end;  (* signature UNIFY *)
