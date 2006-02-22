(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT =
sig
  val inputLine97 : TextIO.instream -> string
  structure Array : COMPAT_ARRAY
  structure Vector : COMPAT_VECTOR
  structure OS :
  sig
    structure Path : COMPAT_PATH
  end
  structure Substring : COMPAT_SUBSTRING
  structure TextIO : COMPAT_TEXT_IO
  structure Timer : COMPAT_TIMER
  structure SocketIO : COMPAT_SOCKET_IO
end;
