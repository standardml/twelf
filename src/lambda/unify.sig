(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  structure IntSyn : INTSYN

  exception Unify of string
	
  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)

  (* unifiable (G, Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* unifiable' (G, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *)
  val unifiable' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option

end;  (* signature UNIFY *)
