(* Field *)
(* Author: Roberto Virga *)

signature FIELD =
sig

  (* Name of the set *)
  val name : string

  (* Main type *)
  eqtype number

  (* Non-invertible element *)
  exception Div

  (* Constants *)
  val zero : number
  val one  : number

  (* Operators *)
  val ~ : number -> number
  val + : number * number -> number
  val - : number * number -> number
  val * : number * number -> number
  val inverse : number -> number  (* raises Div *)

  (* Conversions *)
  val fromInt    : int -> number
  val fromString : string -> number option
  val toString   : number -> string

end;  (* signature FIELD *)

