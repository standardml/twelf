(* Compatibility shim from Basis-current Substring to Basis-97 Substring *)
(* Author: Christopher Richards *)

structure CompatSubstring97 :> COMPAT_SUBSTRING =
struct
  val full = Substring.all
end;
