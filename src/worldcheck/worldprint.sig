(* World Printer *)
(* Author: Carsten Schuermann *)

signature WORLDPRINT =
sig
  structure Formatter : FORMATTER
  (*! structure Tomega : TOMEGA !*)

  exception Error of string 

  val formatWorlds : Tomega.Worlds -> Formatter.format 
  val worldsToString : Tomega.Worlds -> string

end;  (* signature WORLDPRINT *)
