(* Style Checking *)
(* Author: Carsten Schuermann *)

signature STYLECHECK =
sig
  exception Error of string

  val check : unit ->  unit  (* raises Error (msg) *)
  val checkConDec : IntSyn.cid -> unit
end;  (* signature STYLECHECK *)
