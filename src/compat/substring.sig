(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT_SUBSTRING =
sig
  val full : string -> Substring.substring
end;
