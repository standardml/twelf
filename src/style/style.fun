(* Style Checking *)
(* Author: Carsten Schuermann *)

functor StyleCheck (structure Whnf : WHNF
		    structure Index : INDEX
		    structure Origins : ORIGINS)
  : STYLECHECK =
struct
  exception Error of string
   
  local 
    structure I = IntSyn
    structure P = Paths

    datatype polarity = Plus | Minus
      
    fun toggle Plus = Minus
      | toggle Minus = Plus

    fun wrapMsg (c, occ, msg) =  
        (case Origins.originLookup c
	   of (fileName, NONE) => (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) => 
	        (P.wrapLoc' (P.Loc (fileName, P.occToRegionClause occDec occ),
                             Origins.linesInfoLookup (fileName), msg)))

    fun denumber [] = []
      | denumber (c :: l) = 
        let 
	  val x = ord c
	  val l' = denumber l
	in
	  if (x >= 65 andalso x <= 90)
	    orelse (x >= 97 andalso x <= 122) then c :: l' else l'
	end

    fun checkVariablename c (n, n1, occ) =
      if (denumber (explode n) = denumber (explode n1)) then []
      else [wrapMsg (c, occ, "Variable nameing: expected " ^ n ^ " found " ^ n1 ^ "\n")]

    fun styleDec c (I.Dec (SOME n, V), pol, occ) = 
        (case (Names.getNamePref (I.targetFam V)) 
	   of NONE => []
	    | SOME (n1, n2) =>  
	     (case pol 
		of Plus => checkVariablename c (n1, n, occ)
	         | Minus => checkVariablename c (n2, n, occ)))
      | styleDec c (I.Dec (NONE, V), pol, occ) = []

    fun implicitHead (I.BVar k) = 0
      | implicitHead (I.Const c) = I.constImp c
      | implicitHead (I.Skonst k) = 0
      | implicitHead (I.Def d) = I.constImp d
      | implicitHead (I.NSDef d) = I.constImp d
      | implicitHead (I.FgnConst _) = 0

    fun checkExp c ((G, P), I.Uni _, pol, occ) = []
      | checkExp c ((G, P), I.Pi ((D, I.Maybe), V), pol, occ) = 
        (styleDec c (D, toggle pol, occ) @
	 checkDec c ((G, P), D, toggle pol, P.label occ) @
	 checkExp c ((I.Decl (G, D), I.Decl (P, toggle pol)), V, pol, P.body occ))
      | checkExp c ((G, P), I.Pi ((D, I.No), V), pol, occ) = 
        (checkDec c ((G, P), D, toggle pol, P.label occ) @
	 checkExp c ((I.Decl (G, D), I.Decl (P, toggle pol)), V, pol, P.body occ))
      | checkExp c ((G, P), I.Lam (D, U), pol, occ) = 
        (styleDec c (D, toggle pol, occ) @
	 checkDec c ((G, P), D, toggle pol, P.label occ) @
	 checkExp c ((I.Decl (G, D), I.Decl (P, toggle pol)), U, pol, P.body occ))
      | checkExp c ((G, P), I.Root (H, S), pol, occ) = 
	checkHead c ((G, P), H, pol, P.head occ) @
	checkSpine c ((G, P), 1, implicitHead H, S, pol, P.body occ)
      | checkExp c ((G, P), I.FgnExp (_, _), pol, occ) = []

    and checkDec c ((G, P), I.Dec (_, V), pol, occ) = 
          checkExp c ((G, P), V, pol, occ)
	  
    and checkHead c ((G, P), I.BVar k, pol, occ) = 
        styleDec c (I.ctxLookup (G, k), I.ctxLookup (P,k), occ)
      | checkHead c ((G, P), I.Const _, pol, occ) = []
      | checkHead c ((G, P), I.Skonst k, pol, occ) = []
      | checkHead c ((G, P), I.Def d, pol, occ) = []
      | checkHead c ((G, P), I.NSDef d, pol, occ) = []
      | checkHead c ((G, P), I.FgnConst _, pol, occ) = []

    and checkSpine c ((G, P), n, 0, I.Nil, pol, occ) = []
      | checkSpine c ((G, P), n, 0, I.App (U, S), pol, occ) = 
	 (checkExp c ((G, P), U, pol, P.arg (n, occ)) @
	  checkSpine c ((G, P), n+1, 0, S, pol, occ))
      | checkSpine c ((G, P), n, i, S, pol, occ) =
	  checkSpine c ((G, P), n+1, i-1, S, pol, occ)

    fun checkExp' c ((G, P), 0, V, pol, occ) = checkExp c ((G, P), V, pol, occ)
      | checkExp' c ((G, P), n, I.Pi ((D, I.Maybe), V), pol, occ) = 
        (checkExp' c ((I.Decl (G, D), I.Decl (P, toggle pol)), n-1, V, pol, P.body occ))

    fun check' (c, I.ConDec (_, _, _, _, U, V)) =
        (if !Global.chatter > 3
	   then print (Names.qidToString (Names.constQid c) ^ " ")
	 else ();
	 checkExp' c ((I.Null, I.Null), I.constImp c, U, Minus, P.top) @ checkAll (c+1))
      | check' (c, _) = checkAll (c+1)

    and checkAll c = 
        (case I.sgnSize () 
	   of (m, _) => (if c <= m then check' (c, I.sgnLookup c) else []))

    fun check () = (print (concat (checkAll 0)); ())
  in
    val check = check
  end
end
