(* Unification *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature UNIFY =
sig

  (*! structure IntSyn : INTSYN !*)

  type unifTrail

  (* suspending and resuming trailing *)
  val suspend : unit -> unifTrail
  val resume : unifTrail  -> unit

  (* trailing of variable instantiation *)

  val reset       : unit -> unit
  val mark   : unit -> unit
  val unwind : unit -> unit

  val instantiateEVar : IntSyn.Exp option ref * IntSyn.Exp * IntSyn.cnstr list -> unit
  val instantiateLVar : IntSyn.Block option ref * IntSyn.Block -> unit

  val resetAwakenCnstrs : unit -> unit
  val nextCnstr : unit -> IntSyn.cnstr option
  val addConstraint : IntSyn.cnstr list ref * IntSyn.cnstr -> unit
  val solveConstraint : IntSyn.cnstr -> unit

  val delay : IntSyn.eclo * IntSyn.cnstr -> unit

  (* unification *)

  val intersection : IntSyn.Sub * IntSyn.Sub -> IntSyn.Sub

  exception Unify of string

  val unify : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val unifyW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)

  val unifyBlock : IntSyn.dctx * IntSyn.Block * IntSyn.Block -> unit (* raises Unify *)

  val unifySub : IntSyn.dctx * IntSyn.Sub * IntSyn.Sub -> unit  (* raises Unify *)


  val invertible : IntSyn.dctx * IntSyn.eclo * IntSyn.Sub * IntSyn.Exp option ref -> bool
  val invertSub : IntSyn.dctx * IntSyn.Sub * IntSyn.Sub * IntSyn.Exp option ref -> IntSyn.Sub

  (* unifiable (G, Us,Us') will instantiate EVars as an effect *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* unifiable' (G, Us,Us') is like unifiable, but returns NONE for
     success and SOME(msg) for failure *)
  val unifiable' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option

end;  (* signature UNIFY *)
