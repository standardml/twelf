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
	  if x <48 orelse x >57 then c :: l' else l'
	end

    fun checkVariablename c (n, n1, occ) =
      if (denumber (explode n) = denumber (explode n1)) then []
      else [wrapMsg (c, occ, "Variable nameing: expected " ^ n ^ " found " ^ n1 ^ "\n")]

    fun styleDec c (G, I.Dec (SOME n, V), pol, occ) = 
        (case (Names.getNamePref (I.targetFam V)) 
	   of NONE => []
	    | SOME (n1, n2) =>  
	     (case pol 
		of Plus => checkVariablename c (n1, n, occ)
	         | Minus => checkVariablename c (n2, n, occ)))
      | styleDec c (G, I.Dec (NONE, V), pol, occ) = []

    fun implicitHead (I.BVar k) = 0
      | implicitHead (I.Const c) = I.constImp c
      | implicitHead (I.Skonst k) = 0
      | implicitHead (I.Def d) = I.constImp d
      | implicitHead (I.NSDef d) = I.constImp d
      | implicitHead (I.FgnConst _) = 0

	  
    fun checkExp c (G, I.Uni _, pol, occ) = []
      | checkExp c (G, I.Pi ((D, I.Maybe), V), pol, occ) = 
        (styleDec c (G, D, pol, occ) @
	 checkDec c (G, D, toggle pol, P.label occ) @
	 checkExp c (I.Decl (G, D), V, pol, P.body occ))
      | checkExp c (G, I.Pi ((D, I.No), V), pol, occ) = 
        (checkDec c (G, D, toggle pol, P.label occ) @
	 checkExp c (I.Decl (G, D), V, pol, P.body occ))
      | checkExp c (G, I.Lam (D, U), pol, occ) = 
        (styleDec c (G, D, pol, occ) @
	 checkDec c (G, D, toggle pol, P.label occ) @
	 checkExp c (I.Decl (G, D), U, pol, P.body occ))
      | checkExp c (G, I.Root (H, S), pol, occ) = 
	checkHead c (G, H, pol, P.head occ) @
	checkSpine c (G, 0, implicitHead H, S, pol, P.body occ)
      | checkExp c (G, I.FgnExp (_, _), pol, occ) = []

    and checkDec c (G, I.Dec (_, V), pol, occ) = 
          checkExp c (G, V, pol, occ)
	  
    and checkHead c (G, I.BVar k, pol, occ) = 
        styleDec c (G, I.ctxLookup (G, k), pol, occ) 
      | checkHead c (G, I.Const _, pol, occ) = []
      | checkHead c (G, I.Skonst k, pol, occ) = []
      | checkHead c (G, I.Def d, pol, occ) = []
      | checkHead c (G, I.NSDef d, pol, occ) = []
      | checkHead c (G, I.FgnConst _, pol, occ) = []

    and checkSpine c (G, n, 0, I.Nil, pol, occ) = []
      | checkSpine c (G, n, 0, I.App (U, S), pol, occ) = 
	 (checkExp c (G, U, pol, P.arg (n, occ)) @
	  checkSpine c (G, n+1, 0, S, pol, occ))
      | checkSpine c (G, n, i, S, pol, occ) =
	  checkSpine c (G, n+1, i-1, S, pol, occ)

    fun check' (c, I.ConDec (_, _, _, _, U, V)) =
        (if !Global.chatter > 3
	   then print (Names.qidToString (Names.constQid c) ^ " ")
	 else ();
	 checkExp c (I.Null, U, Plus, P.top) @ checkAll (c+1))
      | check' (c, _) = checkAll (c+1)

    and checkAll c = 
        (case I.sgnSize () 
	   of (m, _) => (if c <= m then check' (c, I.sgnLookup c) else []))

    fun check () = (print (concat (checkAll 0)); ())
  in
    val check = check
  end
end
