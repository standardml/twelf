(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  structure IntSyn : INTSYN

  (* trailing of variable instantiation *)

  val reset       : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateEVar : IntSyn.Exp option ref * IntSyn.Exp * IntSyn.cnstr list -> unit
  val addConstraint : IntSyn.cnstr list ref * IntSyn.cnstr -> unit
  val solveConstraint : IntSyn.cnstr -> unit

  val delay : IntSyn.eclo * IntSyn.cnstr -> unit

  (* unification *)

  val intersection : IntSyn.Sub * IntSyn.Sub -> IntSyn.Sub

  exception Unify of string

  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)
  val shape : IntSyn.Exp * IntSyn.Exp -> unit (* raises Unify *)

  val invertible : IntSyn.dctx * IntSyn.eclo * IntSyn.Sub * IntSyn.Exp option ref -> bool
  (* unifiable (G, Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* unifiable' (G, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *)
  val unifiable' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option

end;  (* signature UNIFY *)
