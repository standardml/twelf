(* Origins of Declarations *)
(* Author: Frank Pfenning *)

signature ORIGINS =
sig

  structure IntSyn : INTSYN
  structure Paths : PATHS

  (* val reset : unit -> unit *)
  val installOrigin : IntSyn.cid * (string * Paths.occConDec option) -> unit
  val originLookup : IntSyn.cid -> (string * Paths.occConDec option)

end;  (* signature ORIGINS *)
