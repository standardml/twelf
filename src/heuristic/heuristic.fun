(* Heuristics : Version 1.3 *)
(* Author: Carsten Schuermann *)

structure Heuristic : HEURISTIC = 
struct
  type index = {sd: int,		(* Splitting depth *)
	        ind: (int * int) option,(* Induction variable and depth of induction term *)
	        c: int,			(* Number of cases *)
		m: int,			(* maximal number of cases *)
	        r: int,			(* 0 = non-recursive
					   1 = recursive *)
		p: int}			(* Position (left to right) *)

  local
    fun compare ({sd=k1, ind=NONE, c=c1, m=m1, r=r1, p=p1}, 
		 {sd=k2, ind=NONE, c=c2, m=m2, r=r2, p=p2}) =
        (case (Int.compare (c1*m2, c2*m1), Int.compare (k2, k1), 
	       Int.compare (r1, r2), Int.compare (p1, p2))
	   of (EQUAL, EQUAL, EQUAL, result) => result
	    | (EQUAL, EQUAL, result, _) => result
	    | (EQUAL, result, _, _) => result
	    | (result, _, _, _) => result)
      | compare ({sd=k1, ind=NONE, c=c1, m=m1, r=r1, p=p1}, 
		 {sd=k2, ind=SOME (i2, _), c=c2, m=m2, r=r2, p=p2}) =
	(case (Int.compare (c1*m2, c2*m1)) 
	   of LESS => LESS
	    | EQUAL => GREATER
	    | GREATER => GREATER)
      | compare ({sd=k1, ind=SOME (i1, _), c=c1, m=m1, r=r1, p=p1}, 
		 {sd=k2, ind=NONE, c=c2, m=m2, r=r2, p=p2}) =
	(case (Int.compare (c1*m2, c2*m1)) 
	   of LESS => LESS
	    | EQUAL => LESS
	    | GREATER => GREATER)
      | compare ({sd=k1, ind=SOME (i1, _), c=c1, m=m1, r=r1, p=p1}, 
		 {sd=k2, ind=SOME (i2, _), c=c2, m=m2, r=r2, p=p2}) =
        (case (Int.compare (c1*m2, c2*m1), Int.compare (k2, k1), Int.compare (r1, r2), 
	       Int.compare (i1, i2), Int.compare (p1, p2))
	   of (EQUAL, EQUAL, EQUAL, EQUAL, result) => result
	    | (EQUAL, EQUAL, EQUAL, result, _) => result
	    | (EQUAL, EQUAL, result, _, _) => result
	    | (EQUAL, result, _, _, _) => result
	    | (result, _, _, _, _) => result)


    fun recToString 0 = "non-rec"
      | recToString 1 = "rec"
      
    fun realFmt (r) = Real.fmt (StringCvt.FIX (SOME(2))) r
      
    fun ratio (c, m) = (Real.fromInt c) / (Real.fromInt m)

    fun indexToString {sd, ind=NONE, c, m, r, p} = 
          "(c/m=" ^ (Int.toString c) ^ "/" ^ (Int.toString m) ^ "=" ^
	  (realFmt (ratio (c, m))) ^ 
	  ", ind=., sd=" ^ (Int.toString sd) ^ ", " ^ (recToString r) ^
	  ", p=" ^ (Int.toString p) ^ ")"
	  
      | indexToString {sd, ind=SOME (idx, indd) , c, m, r, p} = 
	  "(c/m=" ^ (Int.toString c) ^ "/" ^ (Int.toString m) ^ "=" ^ 
	  (realFmt (ratio (c, m))) ^ 
	  ", ind=" ^ (Int.toString idx) ^
	  ", indd=" ^ (Int.toString indd) ^
	  ", sd=" ^ (Int.toString sd) ^ ", " ^ (recToString r) ^ 
	  ", p=" ^ (Int.toString p) ^ ")"
	  

  in
    val compare = compare
    val indexToString = indexToString
  end


end; (* functor Heuristic *)