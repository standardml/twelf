(* Rational numbers *)
(* Author: Roberto Virga *)

signature RATIONALS =
sig

  include ORDERED_FIELD

  structure Integers : INTEGERS

  (* Conversions between rationals and integers *)
  val fromInteger : Integers.int -> number

  val floor   : number -> Integers.int
  val ceiling : number -> Integers.int

  (* Basic projections *)
  val numerator : number -> Integers.int
  val denominator : number -> Integers.int

end;  (* signature RATIONALS *)

