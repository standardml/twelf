(* Heuristics : Version 1.3 *)
(* Author: Carsten Schuermann *)

signature HEURISTIC = 
sig
  type index = {sd: int,		(* Splitting depth *)
	        ind: int option,	(* Induction variable *)
	        c: int,			(* Number of cases *)
		m: int,			(* maximal number of cases *)
	        r: int,			(* 0 = non-recursive
					   1 = recursive *)
		p: int}			(* Position (left to right) *)

  val compare : index * index -> order
  val indexToString : index -> string
end; (* signature HEURISTIC *)