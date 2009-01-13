(* String Hash Table *)
(* Author: Frank Pfenning *)

signature STRING_HASH =
sig
  val stringHash : string -> int
  val stringListHash : string list -> int
end;
