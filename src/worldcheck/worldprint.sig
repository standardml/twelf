(* World Printer *)
(* Author: Carsten Schuermann *)

signature WORLDPRINT =
sig
  structure Formatter : FORMATTER
  structure WorldSyn : WORLDSYN

  exception Error of string 

  val formatWorld : WorldSyn.World -> Formatter.format 
  val worldToString : WorldSyn.World -> string
end;  (* signature WORLDPRINT *)
