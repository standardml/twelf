(* World Printer *)
(* Author: Carsten Schuermann *)

signature WORLDPRINT =
sig
  structure Formatter : FORMATTER
  structure WorldSyn : WORLDSYN

  exception Error of string 

  val formatWorlds : WorldSyn.Worlds -> Formatter.format 
  val worldsToString : WorldSyn.Worlds -> string

end;  (* signature WORLDPRINT *)
