(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature VECTOR_SLICE =
sig
  type 'a slice
  val slice : 'a Vector.vector * int * int option -> 'a slice
  val appi : (int * 'a -> unit) -> 'a slice -> unit
  val mapi : (int * 'a -> 'b) -> 'a slice -> 'b Vector.vector
end;
