(* Queues *)
(* Author: Frank Pfenning *)

signature QUEUE =
sig

  type 'a queue

  val empty : 'a queue
  val insert : 'a * 'a queue -> 'a queue
  val delete : 'a queue -> ('a * 'a queue) option

  val insertFront : 'a * 'a queue -> 'a queue
  val deleteEnd : 'a queue -> ('a * 'a queue) option

  (* If  toList (q) ==> (l, SOME(q')) *)
  (* then q == q' and toList q' is constant time *)
  val toList : 'a queue -> 'a list * 'a queue option

end;  (* signature QUEUE *)
