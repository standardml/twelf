(* Total Declarations *)
(* Author: Frank Pfenning *)

functor Total
  (structure Global : GLOBAL
   structure Table : TABLE where type key = int

   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'

   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'

   structure ModeSyn : MODESYN
     sharing ModeSyn.IntSyn = IntSyn'

   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'

   structure Order : ORDER
     sharing Order.IntSyn = IntSyn'
   structure Reduces : REDUCES
     sharing Reduces.IntSyn = IntSyn'

   structure Cover : COVER
     sharing Cover.IntSyn = IntSyn'
     sharing Cover.ModeSyn = ModeSyn

   structure Paths : PATHS
   structure Origins : ORIGINS
     sharing Origins.Paths = Paths
     sharing Origins.IntSyn = IntSyn')
   : TOTAL =
struct
  structure IntSyn = IntSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths

    (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
    val totalTable : unit Table.Table = Table.new(0)

    fun reset () = Table.clear totalTable
    fun install (cid) = Table.insert totalTable (cid, ())
    fun lookup (cid) = Table.lookup totalTable (cid)
  in
    val reset = reset
    val install = install

    fun total (cid) = (* call only on constants *)
        case lookup cid
	  of NONE => false
	   | SOME _ => true

    exception Error' of P.occ * string

    (* copied from terminates/reduces.fun *)
    fun error (c, occ, msg) =  
        (case Origins.originLookup c
	   of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) => 
		raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
					 Origins.linesInfoLookup (fileName),
					 msg)))

    (* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Currently does not allow parametric or hypothetical subgoals.

       Invariants: G |- V[s] : type
    *)
    fun checkClause (G, Vs, occ) = checkClauseW (G, Whnf.whnf Vs, occ)
    and checkClauseW (G, (I.Pi ((D1, I.Maybe), V2), s), occ) =
        (* quantifier *)
        let
	  val D1' = Names.decEName (G, I.decSub (D1, s))
	in
          checkClause (I.Decl (G, D1'), (V2, I.dot1 s), P.body occ)
	end
      | checkClauseW (G, (I.Pi ((D1 as I.Dec (_, V1), I.No), V2), s), occ) =
	(* subgoal *)
	let
	  val _ = checkClause (I.Decl (G, D1), (V2, I.dot1 s), P.body occ)
	in
	  checkGoal (G, (V1, s), P.label occ)
	end
      | checkClauseW (G, (I.Root _, s), occ) =
	(* clause head *)
	()
    and checkGoal (G, Vs, occ) = checkGoalW (G, Whnf.whnf Vs, occ)
    and checkGoalW (G, (I.Pi _, s), occ) =
        raise Error' (occ, "Totality: can not parametric or hypothetical subgoals yet")
      | checkGoalW (G, (V as I.Root (I.Const a, S), s), occ) =	(* s = id *)
	let
	  val _ = if not (total a)
		    then raise Error' (occ, "Subgoal " ^ Names.constName a
				       ^ " not declared to be total")
		  else ()
	in
	  Cover.checkOut (G, V)
	  handle Cover.Error (msg)
	  => raise Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg)
	end

    (* checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun checkOutCover nil = ()
      | checkOutCover (I.Const(c)::cs) =
        ( checkClause (I.Null, (I.constType (c), I.id), P.top)
	     handle Error' (occ, msg) => error (c, occ, msg) ;
          checkOutCover cs )

    (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect:raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun checkFam (a) =
        let
          (* Checking termination *)
	  val _ = (Reduces.checkFam a;
		   if !Global.chatter >= 4
		     then print ("Terminates: " ^ Names.constName a ^ "\n")
		   else ())
	          handle Reduces.Error (msg) => raise Reduces.Error (msg)

          (* Checking input coverage *)
	  (* by termination invariant, there must be consistent mode for a *)
	  val SOME(ms) = ModeSyn.modeLookup a
	  val _ = (Cover.checkCovers (a, ms);
		   if !Global.chatter >= 4
		     then print ("Covers (+): " ^ Names.constName a ^ "\n")
		   else ())
	          handle Cover.Error (msg) => raise Cover.Error (msg)

          (* Checking output coverage *)
          val cs = Index.lookup a
	  val _ = (checkOutCover (cs);
		   if !Global.chatter >= 4
		     then print ("Covers (-): " ^ Names.constName a ^ "\n")
		   else ())
                  handle Cover.Error (msg) => raise Cover.Error (msg)
	in
	  ()
	end
  end

end;  (* functor Total *)
