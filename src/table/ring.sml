(* Rings (aka cyclic lists) *)
(* Author: Carsten Schuermann *)

structure Ring :> RING =
struct

  exception Empty

  type 'a ring = 'a list * 'a list

  (* Representation Invariant:  
     ([an,...,ai+1], [a1,...,ai]) represents
     [a1,...,ai,ai+1,...,an] wrapping around
  *)

  (* empty q = true if q = [], false otherwise *)
  fun empty (nil, nil) = true 
    | empty _ = false

  (* init l = l (as ring) *)
  fun init l = (nil, l)

  (* insert ([], x) = [x]
     insert ([a1, a2 ... an], x) = [x, a1, a2, ... an]
  *)
  fun insert ((r, l), y) = (r, y :: l)

  (* current [] = raise Empty
     current [a1, a2 ... an] = a1
  *)
  fun current (nil, nil) = raise Empty
    | current (_, x :: _) = x
    | current (l, nil) = current (nil, rev l)

  (* next [] = raise Empty
     next [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun next (nil, nil) = raise Empty
    | next (r, nil) = next (nil, rev r)
    | next (r, x :: l) = (x :: r, l)

  (* previous [] = ERROR
     previous [a1, a2 ... an]) = [a2 ... an, a1]
  *)
  fun previous (nil, nil) = raise Empty
    | previous (nil, l) = previous (rev l, nil)
    | previous (x :: r, l) = (r, x :: l)

  (* delete [] = raise Empty
     delete [a1, a2 ... an] = [a2 ... an]
  *)
  fun delete (nil, nil) = raise Empty
    | delete (r, nil) = delete (nil, rev r) 
    | delete (r, x :: l) = (r, l)

  (* foldr is inefficient *)
  fun foldr f i (r, l) = List.foldr f i (l @ rev r)

  (* order of map is undefined.  relevant? *)
  fun map f (r, l) = (List.map f r, List.map f l)

end;  (* structure Ring *)
