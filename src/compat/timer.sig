(* Compatibility shim to cope with Standard Basis version skew *)
(* Author: Christopher Richards *)

signature COMPAT_TIMER =
sig
  val checkCPUTimer : Timer.cpu_timer -> { usr : Time.time, sys : Time.time }
  val checkGCTime : Timer.cpu_timer -> Time.time
end;
