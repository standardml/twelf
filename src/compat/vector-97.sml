(* Compatibility shim from Basis-current Vector to Basis-97 Vector *)
(* Author: Christopher Richards *)

structure CompatVector97 :> COMPAT_VECTOR =
struct
  fun appi f vec = Vector.appi f (vec, 0, NONE)
  fun mapi f vec = Vector.mapi f (vec, 0, NONE)
end;
