(* Total Declarations *)
(* Author: Frank Pfenning *)

signature TOTAL =
sig

  (*! structure IntSyn : INTSYN !*)

  exception Error of string

  val reset : unit -> unit
  val install : IntSyn.cid -> unit	(* install(a) --- a is total in its input arguments *)

  val checkFam : IntSyn.cid -> unit	(* may raise Error(msg) *)

end;  (* signature TOTAL *)
