(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)

signature QUEUE =
sig

  type 'a queue

  val empty : 'a queue
  val insert : 'a * 'a queue -> 'a queue
  val delete : 'a queue -> ('a * 'a queue) option

  (* If  toList (q) ==> (l, SOME(q')) *)
  (* then q == q' and toList q' is constant time *)
  val toList : 'a queue -> 'a list * 'a queue option

end;  (* signature QUEUE *)


structure Queue :> QUEUE =
struct

  (* Representation invariant:
     If  q = (inp, out)  then  q == out @ rev(inp)
  *)
  type 'a queue = 'a list * 'a list

  val empty = (nil, nil)

  fun insert (x, (inp, out)) = (x::inp, out)

  fun delete (nil, nil) = NONE
    | delete (inp, x::out) = SOME (x, (inp, out))
    | delete (inp, nil) = delete (nil, List.rev inp)

  (* toList q ==> (l, NONE)  means q == l and toList is constant time *)
  (* toList q ==> (l, SOME(q')) means q == l == q' *)
  (* and toList q' is constant time *)
  fun toList (nil, out) = (out, NONE)
    | toList (inp, out) =
      let
	val out' = out @ List.rev(inp)
      in
	(out', SOME (nil, out'))
      end

end;  (* structure Queue *)
