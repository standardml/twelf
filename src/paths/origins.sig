(* Origins of Declarations *)
(* Author: Frank Pfenning *)

signature ORIGINS =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure Paths : PATHS !*)

  (* resets all mappings *)
  val reset : unit -> unit

  (* maintains a mapping from file names to line info information *)
  val installLinesInfo : string * Paths.linesInfo -> unit
  val linesInfoLookup  : string -> Paths.linesInfo option

  (* maintains a mapping from constant ids to file names and occurrence trees *)
  val installOrigin : IntSyn.cid * (string * Paths.occConDec option) -> unit
  val originLookup  : IntSyn.cid -> (string * Paths.occConDec option)

  (* maintains a mapping from module ids to file names and regions *)
  val installMOrigin : IntSyn.mid * (string * Paths.region) -> unit
  val mOriginLookup  : IntSyn.mid -> (string * Paths.region)

end;  (* signature ORIGINS *)
