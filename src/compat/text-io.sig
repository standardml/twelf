(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT_TEXT_IO =
sig
  val inputLine : TextIO.instream -> string option
end;
