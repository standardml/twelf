(* Queues *)
(* Author: Frank Pfenning *)
(* Standard functional implementation of queues *)
(*
   Since in the typical use `delete' is not of constant amortized time we
   provide a special `toList' operation which permits constant
   amortized access under programmer control.
*)

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

  fun insertFront (x, (inp, out)) = (inp, x::out)

  fun deleteEnd (nil, nil) = NONE
    | deleteEnd (x::inp, out) = SOME (x, (inp, out))
    | deleteEnd (nil, out) = delete (List.rev out, nil)

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
