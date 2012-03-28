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
    fun recToString 0 = "non-rec = 2"
      | recToString 1 = "rec = 1"

    fun realFmt (r) = Real.fmt (StringCvt.FIX (SOME(2))) r

    fun ratio (0, 0) = 1.0
      | ratio (c, 0) = 1.1
      | ratio (c, m) = (Real.fromInt c) / (Real.fromInt m)


    fun sqr (x:real) = x * x;

    (* sum of the parameters k1 + m1/c1 + 1/ind + r1 *)
    (* the higher the sum the more preferred it is;  *)
    (* - bp Sep 21 1999 - weight splitting depth higher *)
    fun sum {sd=k1, ind=NONE, c=c1, m=m1, r=r1, p=p1} =
      if (c1 = 0) then
        (sqr(Real.fromInt k1) ) + (5.0 - ratio(c1,m1)) + (Real.fromInt r1)
      else
        (sqr(Real.fromInt k1) ) + (1.0 - ratio(c1,m1)) + (Real.fromInt r1)
        | sum {sd=k1, ind=SOME (0), c=c1, m=m1, r=r1, p=p1} =
        if (c1 = 0) then
          (sqr(Real.fromInt k1) ) + (5.0 - ratio(c1,m1)) + (Real.fromInt r1)
        else
          (sqr(Real.fromInt k1)) + ratio(3,2) + (1.0 - ratio(c1,m1)) + (Real.fromInt r1)
        | sum {sd=k1, ind=SOME (i1), c=c1, m=m1, r=r1, p=p1} =
          if (c1 = 0) then
            (sqr(Real.fromInt k1) ) + (5.0 - ratio(c1,m1)) + (Real.fromInt r1)
          else
            (sqr(Real.fromInt k1)) + ratio(1,i1) + (1.0 - ratio(c1,m1)) + (Real.fromInt r1)

    (* associate a higher value to non-rec than to rec  *)
    fun conv{sd=k1, ind=i, c=c1, m=m1, r=1, p=p1} =
        {sd=k1, ind=i, c=c1, m=m1, r=1, p=p1}
      | conv {sd=k1, ind=i, c=c1, m=m1, r=0, p=p1} =
        {sd=k1, ind=i, c=c1, m=m1, r=2, p=p1}


    fun ccompare ({sd=k1, ind=i1, c=c1, m=m1, r=r1, p=p1},
                  {sd=k2, ind=i2, c=c2, m=m2, r=r2, p=p2}) =
        (case (Real.compare (sum{sd=k2, ind=i2, c=c2, m=m2, r=r2, p=p2},
                             sum{sd=k1, ind=i1, c=c1, m=m1, r=r1, p=p1}),
               Int.compare (p1, p2))           (* p                 *)
             of  (EQUAL, result) => result
           | (result, _) => result)

    fun compare ({sd=k1, ind=i1, c=c1, m=m1, r=r1, p=p1},
                 {sd=k2, ind=i2, c=c2, m=m2, r=r2, p=p2}) =
        ccompare (conv({sd=k1, ind=i1, c=c1, m=m1, r=r1, p=p1}),
                  conv({sd=k2, ind=i2, c=c2, m=m2, r=r2, p=p2}))

    fun indexToString {sd=s1, ind=NONE, c=c1, m=m1, r=0, p=p1} =
          "(sd * r =" ^ (Int.toString (s1 * 3)) ^
          ", sd=" ^ (Int.toString s1) ^ ", " ^ (recToString 0) ^ " = 2" ^
          ", c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (1.0 - ratio (c1, m1))) ^
          ", ind=.,"^
          ", p=" ^ (Int.toString p1) ^ " sum = " ^ realFmt(sum {sd=s1, ind=NONE, c=c1, m=m1, r=2, p=p1}) ^ " )"
      | indexToString {sd=s1, ind=NONE, c=c1, m=m1, r=1, p=p1} =
          "(sd * r =" ^ (Int.toString (s1 * 1)) ^
          ", sd=" ^ (Int.toString s1) ^ ", " ^ (recToString 1) ^ " = 1" ^
          ", c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (1.0 - ratio (c1, m1))) ^
          ", ind=.,"^
          ", p=" ^ (Int.toString p1) ^ " sum = " ^ realFmt(sum {sd=s1, ind=NONE, c=c1, m=m1, r=1, p=p1}) ^ " )"
      | indexToString {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=0, p=p1} =
          let
              val i = if idx = 0 then 0.0 else (ratio(1,idx))
          in
          "(sd * r =" ^ (Int.toString (s1 * 3)) ^
          ", sd=" ^ (Int.toString s1) ^ ", " ^ (recToString 0) ^ " = 2" ^
          ", c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (1.0 - ratio (c1, m1))) ^
          ", ind=" ^ (Int.toString idx) ^ " = " ^realFmt(i) ^
          ", p=" ^ (Int.toString p1) ^ " sum = " ^ realFmt(sum {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=2, p=p1}) ^ ")"
          end
      | indexToString {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=1, p=p1} =
          let
              val i = if idx = 0 then 0.0 else (ratio(1,idx))
          in
          "(sd * r =" ^ (Int.toString (s1 * 1)) ^
          ", sd=" ^ (Int.toString s1) ^ ", " ^ (recToString 1) ^ " =  1" ^
          ", c/m=" ^ (Int.toString c1) ^ "/" ^ (Int.toString m1) ^ "=" ^
          (realFmt (1.0 - ratio (c1, m1))) ^
          ", ind=" ^ (Int.toString idx) ^ " = " ^ (realFmt i) ^
          ", p=" ^ (Int.toString p1) ^ " sum = " ^ realFmt(sum {sd=s1, ind=SOME (idx) , c=c1, m=m1, r=1, p=p1}) ^ ")"
          end
  in
    val compare = compare
    val indexToString = indexToString
  end


end; (* functor Heuristic *)