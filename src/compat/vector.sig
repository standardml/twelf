(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT_VECTOR =
sig
  val appi : (int * 'a -> unit) -> 'a Vector.vector -> unit
  val mapi : (int * 'a -> 'b) -> 'a Vector.vector -> 'b Vector.vector
end;
