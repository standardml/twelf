(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT_ARRAY =
sig
  val appi : (int * 'a -> unit) -> 'a Array.array -> unit
end;
