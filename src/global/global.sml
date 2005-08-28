(* Global parameters *)
(* Author: Frank Pfenning *)

structure Global :> GLOBAL =
struct

  val chatter = ref 3
  val style = ref 0
  val maxCid = 19999
  val maxMid = 999
  val maxCSid = 49
  val doubleCheck = ref true
  val unsafe = ref false
  val autoFreeze = ref true (* !!!reconsider later!!! Thu Mar 10 09:42:28 2005 *)
  val timeLimit = ref (NONE : (Time.time option))

  fun chPrint n s = if !chatter >= n then print (s ()) else ()

end;  (* structure Global *)
