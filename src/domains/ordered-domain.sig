(* Ordered Field *)
(* Author: Roberto Virga *)

signature ORDERED_DOMAIN =
sig

  include DOMAIN

  val sign : number -> int
  val abs  : number -> number

  val > : number * number -> bool
  val < : number * number -> bool
  val >= : number * number -> bool
  val <= : number * number -> bool
  val compare : number * number -> order

end;  (* signature ORDERED_DOMAIN *)

