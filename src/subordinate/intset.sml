(* Persistent red/black trees *)
(* Specialized for subordination *)
(* Author: Frank Pfenning *)
(* Copied from src/table/red-black-tree.fun *)

signature INTSET =
sig
  type intset
  val empty : intset
  val insert : int * intset -> intset
  val member : int * intset -> bool
  val foldl : (int * 'b -> 'b) -> 'b -> intset -> 'b
end;

structure IntSet :> INTSET =
struct

  datatype rbt =
    Empty				(* considered black *)
  | Red of int * rbt * rbt
  | Black of int * rbt * rbt

  (* Representation Invariants *)
  (*
     1. The tree is ordered: for every node Red((key1,datum1), left, right) or
        Black ((key1,datum1), left, right), every key in left is less than
        key1 and every key in right is greater than key1.

     2. The children of a red node are black (color invariant).

     3. Every path from the root to a leaf has the same number of
        black nodes, called the black height of the tree.
  *)

  local

  fun lookup dict x =
    let
      fun lk (Empty) = false
	| lk (Red tree) = lk' tree
        | lk (Black tree) = lk' tree
      and lk' (x1, left, right) =
	    (case Int.compare(x,x1)
	       of EQUAL => true
	        | LESS => lk left
		| GREATER => lk right)
      in
	lk dict
      end

  (* val restore_right : 'a dict -> 'a dict *)
  (*
     restore_right (Black(e,l,r)) >=> dict
     where (1) Black(e,l,r) is ordered,
           (2) Black(e,l,r) has black height n,
	   (3) color invariant may be violated at the root of r:
               one of its children might be red.
     and dict is a re-balanced red/black tree (satisfying all invariants)
     and same black height n.
  *)
  fun restore_right (Black(e, Red lt, Red (rt as (_,Red _,_)))) =
         Red(e, Black lt, Black rt)	(* re-color *)
    | restore_right (Black(e, Red lt, Red (rt as (_,_,Red _)))) =
         Red(e, Black lt, Black rt)	(* re-color *)
    | restore_right (Black(e, l, Red(re, Red(rle, rll, rlr), rr))) =
	 (* l is black, deep rotate *)
	 Black(rle, Red(e, l, rll), Red(re, rlr, rr))
    | restore_right (Black(e, l, Red(re, rl, rr as Red _))) =
	 (* l is black, shallow rotate *)
	 Black(re, Red(e, l, rl), rr)
    | restore_right dict = dict

  (* restore_left is like restore_right, except *)
  (* the color invariant may be violated only at the root of left child *)
  fun restore_left (Black(e, Red (lt as (_,Red _,_)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red (lt as (_,_,Red _)), Red rt)) =
	 Red(e, Black lt, Black rt)	(* re-color *)
    | restore_left (Black(e, Red(le, ll as Red _, lr), r)) =
	 (* r is black, shallow rotate *)
	 Black(le, ll, Red(e, lr, r))
    | restore_left (Black(e, Red(le, ll, Red(lre, lrl, lrr)), r)) =
	 (* r is black, deep rotate *)
	 Black(lre, Red(le, ll, lrl), Red(e, lrr, r))
    | restore_left dict = dict

  fun insert (dict, x) =
    let
      (* val ins : 'a dict -> 'a dict  inserts entry *)
      (* ins (Red _) may violate color invariant at root *)
      (* ins (Black _) or ins (Empty) will be red/black tree *)
      (* ins preserves black height *)
      fun ins (Empty) = Red(x, Empty, Empty)
	| ins (Red(x1, left, right)) =
	  (case Int.compare(x,x1)
	     of EQUAL => Red(x, left, right)
	      | LESS => Red(x1, ins left, right)
	      | GREATER => Red(x1, left, ins right))
	| ins (Black(x1, left, right)) =
	  (case Int.compare(x,x1)
	     of EQUAL => Black(x, left, right)
	      | LESS => restore_left (Black(x1, ins left, right))
	      | GREATER => restore_right (Black(x1, left, ins right)))
    in
      case ins dict
	of Red (t as (_, Red _, _)) => Black t (* re-color *)
	 | Red (t as (_, _, Red _)) => Black t (* re-color *)
	 | dict => dict
    end
  in
    type intset = rbt
    val empty = Empty
    val insert = fn (x,t) => insert (t, x)
    val member = fn (x,t) => lookup t x
    fun foldl f a t =
        let fun fo (Empty, r) = r
              | fo (Red (x, left, right), r) =
	          fo (right, f (x, fo (left, r)))
              | fo (Black (x, left, right), r) =
		  fo (right, f (x, fo (left, r)))
	in
	  fo (t, a)
	end
  end

end;  (* structure IntSet *)
