(* Ordered Field *)
(* Author: Roberto Virga *)

signature ORDERED_FIELD =
sig

  include FIELD

  (* Sign operations *)
  val sign : number -> int
  val abs  : number -> number

  (* Comparisons predicates *)
  val > : number * number -> bool
  val < : number * number -> bool
  val >= : number * number -> bool
  val <= : number * number -> bool
  val compare : number * number -> order

end;  (* signature ORDERED_FIELD *)

