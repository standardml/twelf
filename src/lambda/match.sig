(* Matching *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature MATCH =
sig

  (*! structure IntSyn : INTSYN !*)

  (* matching *)
  exception Match of string

  val match : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit	(* raises Unify *)
  val matchW : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> unit (* raises Unify *)

  val matchBlock : IntSyn.dctx * IntSyn.Block * IntSyn.Block -> unit (* raises Unify *)

  val matchSub : IntSyn.dctx * IntSyn.Sub * IntSyn.Sub -> unit  (* raises Unify *)

  (* instance (G, Us,Us') will instantiate EVars as an effect 
     checks if Us' is an instance of Us *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool

  (* instance' (G, Us,Us') is like instance, but returns NONE for
     success and SOME(msg) for failure *)
  val instance' : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> string option

end;  (* signature MATCH *)
