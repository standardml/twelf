(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature MONO_ARRAY_SLICE =
sig
  type array
  type slice
  type vector
  val slice : array * int * int option -> slice
  val vector : slice -> vector
end;
