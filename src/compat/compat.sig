(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT =
sig
  structure Array : COMPAT_ARRAY
  structure Vector : COMPAT_VECTOR
  structure OS :
  sig
    structure Path : COMPAT_PATH
  end
  structure Timer : COMPAT_TIMER
end;
