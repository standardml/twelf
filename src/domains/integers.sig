(* Integers *)
(* Author: Roberto Virga *)

signature INTEGERS =
sig
  include INTEGER

  val gcd : int * int -> int
  val lcm : int * int -> int
  val solve_gcd : int * int -> int * int
end;  (* signature INTEGERS *)

