(* Heuristics : Version 1.3 *)
(* Author: Carsten Schuermann *)

structure Heuristic : HEURISTIC =
struct
  type index = {sd: int,                (* Splitting depth *)
                ind: int option,        (* Induction variable *)
                c: int,                 (* Number of cases *)
                m: int,                 (* maximal number of cases *)
                r: int,                 (* 0 = non-recursive
                                           1 = recursive *)
                p: int}                 (* Position (left to right) *)

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
                 {sd=k2, ind=SOME (i2), c=c2, m=m2, r=r2, p=p2}) =
        (case (Int.compare (c1*m2, c2*m1))
           of LESS => LESS
            | EQUAL => GREATER
            | GREATER => GREATER)
      | compare ({sd=k1, ind=SOME (i1), c=c1, m=m1, r=r1, p=p1},
                 {sd=k2, ind=NONE, c=c2, m=m2, r=r2, p=p2}) =
        (case (Int.compare (c1*m2, c2*m1))
           of LESS => LESS
            | EQUAL => LESS
            | GREATER => GREATER)
      | compare ({sd=k1, ind=SOME (i1), c=c1, m=m1, r=r1, p=p1},
                 {sd=k2, ind=SOME (i2), c=c2, m=m2, r=r2, p=p2}) =
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

    fun sum {sd=k1, ind=NONE, c=c1, m=m1, r=r1, p=p1} =
        realFmt ((Real.fromInt k1) + ratio(m1,c1) + (Real.fromInt r1))
        | sum {sd=k1, ind=SOME (i1), c=c1, m=m1, r=r1, p=p1} =
        realFmt ((Real.fromInt k1) + ratio(1,i1) + ratio(m1,c1) + (Real.fromInt r1))

    fun indexToString {sd = s1, ind=NONE, c=c1, m=m1, r=r1, p=p1} =
          "(c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (ratio (c1, m1))) ^
          ", ind=., sd=" ^ (Int.toString s1) ^ ", " ^ (recToString r1) ^
          ", p=" ^ (Int.toString p1) ^ "sum = " ^ (sum {sd=s1, ind=NONE, c=c1, m=m1, r=r1, p=p1}) ^ " )"

      | indexToString {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=r1, p=p1} =
          "(c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (ratio (c1, m1))) ^
          ", ind=" ^ (Int.toString idx) ^
          ", sd=" ^ (Int.toString s1) ^ ", " ^ (recToString r1) ^
          ", p=" ^ (Int.toString p1) ^ " sum = " ^ (sum {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=r1, p=p1}) ^ ")"


  in
    val compare = compare
    val indexToString = indexToString
  end


end; (* functor Heuristic *)