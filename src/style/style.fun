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

    fun options (n :: nil) = n
      | options (n :: l) = n ^ ", " ^ (options l)

    fun checkVariablename c (n, prefNames, occ) =
      if List.exists (fn n' => (denumber (explode n) = denumber (explode n'))) prefNames then []
      else [wrapMsg (c, occ, "Variable naming: expected " ^ options prefNames ^ " found " ^ n ^ "\n")]

    fun styleDec c (I.Dec (SOME n, V), pol, occ) = 
        (case (Names.getNamePref (I.targetFam V)) 
	   of NONE => []
	    | SOME (prefENames, prefUNames) =>  
	     (case pol 
		of Plus => checkVariablename c (n, prefENames, occ)
	         | Minus => checkVariablename c (n, prefUNames, occ)))
      | styleDec c (I.Dec (NONE, V), pol, occ) = []

    fun implicitHead (I.BVar k) = 0
      | implicitHead (I.Const c) = I.constImp c
      | implicitHead (I.Skonst k) = 0
      | implicitHead (I.Def d) = I.constImp d
      | implicitHead (I.NSDef d) = I.constImp d
      | implicitHead (I.FgnConst _) = 0


    fun checkExp c ((G, P), I.Uni _, occ) = []
      | checkExp c ((G, P), I.Lam (D, U), occ) = 
        (checkDec c ((G, P), D, Plus, P.label occ) @
	 checkExp c ((I.Decl (G, D), I.Decl (P, Minus)), U, P.body occ))
      | checkExp c ((G, P), I.Root (H, S), occ) = 
	checkHead c ((G, P), H, P.head occ) @
	checkSpine c ((G, P), 1, implicitHead H, S, P.body occ)
      | checkExp c ((G, P), I.FgnExp (_, _), occ) = []

    and checkType c ((G, P), I.Uni _, pol, occ) = []
      | checkType c ((G, P), I.Pi ((D, I.Maybe), V), pol, occ) = 
        (checkDec c ((G, P), D, toggle pol, P.label occ) @
	 checkType c ((I.Decl (G, D), I.Decl (P, pol)), V, pol, P.body occ))
      | checkType c ((G, P), I.Pi ((D, I.No), V), pol, occ) = 
        (checkDec c ((G, P), D,  toggle pol, P.label occ) @
	 checkType c ((I.Decl (G, D), I.Decl (P, pol)), V, pol, P.body occ))
      | checkType c ((G, P), I.Root (H, S), pol, occ) = 
	checkHead c ((G, P), H, P.head occ) @
	checkSpine c ((G, P), 1, implicitHead H, S, P.body occ)
      | checkType c ((G, P), I.FgnExp (_, _), pol, occ) = []

    and checkDec c ((G, P), I.Dec (_, V), pol, occ) = 
          checkType c ((G, P), V, pol, occ)
	  
    and checkHead c ((G, P), I.BVar k, occ) = 
        styleDec c (I.ctxLookup (G, k), I.ctxLookup (P,k), occ)
      | checkHead c ((G, P), I.Const _, occ) = []
      | checkHead c ((G, P), I.Skonst k, occ) = []
      | checkHead c ((G, P), I.Def d, occ) = []
      | checkHead c ((G, P), I.NSDef d, occ) = []
      | checkHead c ((G, P), I.FgnConst _, occ) = []

    and checkSpine c ((G, P), n, 0, I.Nil, occ) = []
      | checkSpine c ((G, P), n, 0, I.App (U, S), occ) = 
	 (checkExp c ((G, P), U, P.arg (n, occ)) @
	  checkSpine c ((G, P), n+1, 0, S, occ))
      | checkSpine c ((G, P), n, i, S, occ) =
	  checkSpine c ((G, P), n+1, i-1, S, occ)

    fun checkType' c ((G, P), 0, V, pol, occ) = checkType c ((G, P), V, pol, occ)
      | checkType' c ((G, P), n, I.Pi ((D, I.Maybe), V), pol, occ) = 
        (checkType' c ((I.Decl (G, D), I.Decl (P, pol)), n-1, V, pol, P.body occ))

    fun checkExp' c ((G, P), 0, V,  occ) = checkExp c ((G, P), V,  occ)
      | checkExp' c ((G, P), n, I.Pi ((D, I.Maybe), V), occ) = 
        (checkExp' c ((I.Decl (G, D), I.Decl (P, Plus)), n-1, V, P.body occ))

    fun checkConDec c (I.ConDec (_, _, implicit, _, U, V)) =
        (if !Global.chatter > 3
	   then print (Names.qidToString (Names.constQid c) ^ " ")
	 else ();
	   checkType' c ((I.Null, I.Null), implicit, U, Plus, P.top))
      | checkConDec c (I.ConDef (_, _, implicit,  _, U, _, _)) =
	   (if !Global.chatter > 3
	      then print (Names.qidToString (Names.constQid c) ^ " ")
	    else ();
	   checkType' c ((I.Null, I.Null), implicit, U, Plus, P.top))

    fun checkAll (c, n) = 
        (if c <= n then checkConDec c (I.sgnLookup c) @ checkAll (c+1, n) else [])

    fun check () = 
      let 
	val (n, _) = I.sgnSize () 
      in (map print (checkAll (0, n)); ())
      end
 
  in
    val checkConDec = (fn c => (map print (checkConDec c (I.sgnLookup c)); ()))
    val check = check
  end
end
