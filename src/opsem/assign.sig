(* Assignment *)
(* Author: Larry Greenfield *)

signature ASSIGN =
sig
  structure IntSyn : INTSYN

  exception Assign of string

  (* raises Assign, instantiates EVars as effect *)
  val assign : IntSyn.eclo * IntSyn.eclo -> unit

  (* assigniable (Us,Us') will instantiate EVars as an effect *)
  val assignable : IntSyn.eclo * IntSyn.eclo -> bool
end;
