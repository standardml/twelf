(* Total Declarations *)
(* Author: Frank Pfenning *)

signature TOTAL =
sig

  structure IntSyn : INTSYN

  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit	(* other info with termination order *)

  val checkFam : IntSyn.cid -> unit

end;  (* signature TOTAL *)
