(* Global parameters *)
(* Author: Frank Pfenning *)

structure Global :> GLOBAL =
struct

  val chatter = ref 3
  val maxCid = 9999
  val doubleCheck = ref false
  val safe = ref true
end;  (* structure Global *)
