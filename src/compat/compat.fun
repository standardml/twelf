(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

functor Compat
  (structure Array : COMPAT_ARRAY
   structure Vector : COMPAT_VECTOR
   structure Path : COMPAT_PATH
   structure Timer : COMPAT_TIMER
  )
  : COMPAT =
struct
  structure Array = Array
  structure Vector = Vector
  structure OS =
    struct
      structure Path = Path
    end
  structure Timer = Timer
end;
