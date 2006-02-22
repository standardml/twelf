(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

functor Compat
  (structure Array : COMPAT_ARRAY
   structure Vector : COMPAT_VECTOR
   structure Path : COMPAT_PATH
   structure Substring : COMPAT_SUBSTRING
   structure TextIO : COMPAT_TEXT_IO
   structure Timer : COMPAT_TIMER
   structure SocketIO : COMPAT_SOCKET_IO
  )
  : COMPAT =
struct
  structure Array = Array
  structure Vector = Vector
  structure OS =
    struct
      structure Path = Path
    end
  structure Substring = Substring
  structure TextIO = TextIO
  structure Timer = Timer
  structure SocketIO = SocketIO
  fun inputLine97 instream = getOpt (TextIO.inputLine instream, "")
end;
