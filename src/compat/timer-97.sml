(* Compatibility shim from Basis-current Timer to Basis-97 Timer *)
(* Author: Christopher Richards *)

structure CompatTimer97 :> COMPAT_TIMER =
struct
  fun checkCPUTimer timer =
      let
	val {usr = usr, sys = sys, gc = gc} = Timer.checkCPUTimer timer
      in
	{usr = usr, sys = sys}
      end
      
  fun checkGCTime timer =
      let
	val {gc = gc, ...} = Timer.checkCPUTimer timer
      in
	gc
      end
end;
