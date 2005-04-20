(* Worldification *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor Worldify
  (structure Global : GLOBAL
   (*! structure IntSyn : INTSYN !*)
   (*! structure Tomega : TOMEGA !*)
   (*! sharing Tomega.IntSyn = IntSyn !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn !*)
   (*! sharing WorldSyn.Tomega = Tomega !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn !*)
   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn !*)
   structure Unify : UNIFY
   (*! sharing Unify.IntSyn = IntSyn !*)
   structure Abstract : ABSTRACT
   (*! sharing Abstract.IntSyn = IntSyn !*)
   structure Constraints : CONSTRAINTS
   (*! sharing Constraints.IntSyn = IntSyn !*)
   structure CSManager : CS_MANAGER
   (*! sharing CSManager.IntSyn = IntSyn !*)
   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn !*)

   structure Table : TABLE where type key = int
   structure MemoTable : TABLE where type key = int * int
   structure IntSet : INTSET

   (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
   (*! sharing Origins.IntSyn = IntSyn !*)
       )
   : WORLDIFY = 
struct
  (*! structure IntSyn = IntSyn !*)
  (*! structure Tomega = Tomega !*)
  structure I = IntSyn
  structure T = Tomega
  structure P = Paths
  structure F = Print.Formatter

  exception Error of string 

  exception Error' of P.occ * string


  (* World Subsumption graph

       World subsumption Graph is valid
       iff for any type families a and b
       if b > a then there a path from b to a in the graph.

       World subsumption is transitive and reflexive.
  *)
  val subGraph : (IntSet.intset) Table.Table = Table.new (32)
  val insert = Table.insert subGraph
  fun adjNodes a = valOf (Table.lookup subGraph a)  (* must be defined! *)
  fun insertNewFam a =
        Table.insert subGraph (a, IntSet.empty)
  val updateFam = Table.insert subGraph
    
  (* memotable to avoid repeated graph traversal *)
  (* think of hash-table model *)
  val memoTable : (bool * int) MemoTable.Table = MemoTable.new (2048)
  val memoInsert = MemoTable.insert memoTable
  val memoLookup = MemoTable.lookup memoTable
  val memoClear = fn () => MemoTable.clear memoTable
  val memoCounter = ref 0


  (* copied from terminates/reduces.fun *)
  fun wrapMsg (c, occ, msg) =  
      (case Origins.originLookup c
	 of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) => 
		(P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                             Origins.linesInfoLookup (fileName),
                             "Constant " ^ Names.qidToString (Names.constQid c) ^ "\n" ^ msg)))

  type dlist = IntSyn.Dec list


  local
    structure W = WorldSyn
   
    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    datatype Reg			(* Regular world expressions  *)
      = Block of I.cid * (I.dctx * dlist)		(* R ::= LD                   *)
      | Seq of int * dlist * I.Sub	(*     | (Di,...,Dn)[s]       *)
      | Star of Reg			(*     | R*                   *)
      | Plus of Reg * Reg		(*     | R1 + R2              *)
      | One				(*     | 1                    *)

    exception Success of I.Exp			(* signals worldcheck success *)

    (* createEVarSub G G' = s
     
       Invariant:
       If   G is a context
       and  G' is a context
       then G |- s : G'
    *)
    fun createEVarSub (G, I.Null) = I.Shift (I.ctxLength G)
      | createEVarSub (G, I.Decl(G', D as I.Dec (_, V))) =
        let
	  val s = createEVarSub (G, G')
	  val V' = I.EClo (V, s)
	  val X = I.newEVar (G, V')
	in
	  I.Dot (I.Exp X, s)
	end

    (* from cover.fun *)
    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars in Xs

       try simplifying away the constraints in case they are "hard"
    *)
    fun collectConstraints (nil) = nil
      | collectConstraints (I.EVar (_, _, _, ref nil)::Xs) =
          collectConstraints Xs
      | collectConstraints (I.EVar (_, _, _, ref constrs)::Xs) =
	  (* constrs <> nil *)
          Constraints.simplify constrs @ collectConstraints Xs

    (* collectEVars (G, s, Xs) = Xs'
       adds all uninstantiated EVars from s to Xs to obtain Xs'
       Invariant: s is EVar substitutions
    *)
    fun collectEVars (G, I.Dot (I.Exp X, s), Xs) = 
           collectEVars (G, s, Abstract.collectEVars (G, (X, I.id), Xs))
      | collectEVars (G, I.Shift _, Xs) = Xs
      (* other cases impossible by invariants since s is EVarSubst *)
      
    (* noConstraints (G, s) = true iff there are no remaining constraints in s
       Invariants: s is an EVar substitution X1...Xn.^k
    *)
    fun noConstraints (G, s) =
        (case collectConstraints (collectEVars (G, s, nil))
	   of nil => true
	    | _ => false)
    (* end from cover.fun *)

    (************)
    (* Printing *)
    (************)

    (* Declarations *)
    fun formatD (G, D) =
          F.Hbox (F.String "{" :: Print.formatDec (G, D) :: F.String "}" :: nil)

    (* Declaration lists *)
    fun formatDList (G, nil, t) = nil
      | formatDList (G, D :: nil, t) =
        let
	  val D' = I.decSub (D, t)
	in
          formatD (G, D') :: nil (* Names.decUName (G, I.decSub(D, t)) *)
	end
      | formatDList (G, D :: L, t) = 
        let
	  val D' = I.decSub (D, t) (* Names.decUName (G, I.decSub (D, t)) *)
	in 
	  formatD (G, D') :: F.Break
	  :: formatDList (I.Decl (G, D'), L, I.dot1 t)
	end

    (*
    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V
    *)

    (* Hypotheses and declaration lists *)
    fun wGoalToString ((G, L), Seq (_, piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, L, I.id)), F.Break,
				   F.String "<|", F.Break,
				   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    fun worldToString (G, Seq (_, piDecs, t)) =
          F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))

    (* Hypotheses *)
    fun hypsToString (G, L) =
          F.makestring_fmt (F.HVbox (formatDList (G, L, I.id)))

    (* Mismatch between hypothesis and world declaration *)
    fun mismatchToString (G, (V1, s1), (V2, s2)) =
        F.makestring_fmt (F.HVbox [Print.formatExp (G, I.EClo (V1, s1)), F.Break,
				   F.String "<>", F.Break,
				   Print.formatExp (G, I.EClo (V2, s2))])

    (***********)
    (* Tracing *)
    (***********)

    structure Trace :
    sig
      val clause : I.cid -> unit
      val constraintsRemain : unit -> unit
      val matchBlock : (I.dctx * dlist) * Reg -> unit
      val unmatched : I.dctx * dlist -> unit
      val missing : I.dctx * Reg -> unit
      val mismatch : I.dctx * I.eclo * I.eclo -> unit
      val success : unit -> unit
    end =
    struct
      fun clause (c) =
          print ("World checking clause " ^ Names.qidToString (Names.constQid c) ^ "\n")
      fun constraintsRemain () =
	  if !Global.chatter > 7
	    then print ("Constraints remain after matching hypotheses against context block\n")
	  else ()
      fun matchBlock (GL, R) =		(* R = (D1,...,Dn)[t] *)
	  if !Global.chatter > 7
	    then print ("Matching:\n" ^ wGoalToString (GL, R) ^ "\n")
	  else ()
      fun unmatched GL =
	  if !Global.chatter > 7
	    then print ("Unmatched hypotheses:\n" ^ hypsToString GL ^ "\n")
	  else ()
      fun missing (G, R) =		(* R = (D1,...,Dn)[t] *)
	  if !Global.chatter > 7
	    then print ("Missing hypotheses:\n" ^ worldToString (G, R) ^ "\n")
	  else ()
      fun mismatch (G, Vs1, Vs2) =
	  if !Global.chatter > 7
	    then print ("Mismatch:\n" ^ mismatchToString (G, Vs1, Vs2) ^ "\n")
	  else ()
      fun success () =
	  if !Global.chatter > 7
	    then print ("Success\n")
	  else ()
    end

    fun decUName (G, D) = I.Decl (G, Names.decUName (G, D))
    fun decEName (G, D) = I.Decl (G, Names.decEName (G, D))

    (**************************************)
    (* Matching hypotheses against worlds *)
    (**************************************)

    fun subGoalToDList (I.Pi ((D, _), V)) = D::subGoalToDList(V)
      | subGoalToDList (I.Root _) = nil

    (* worldsToReg (Worlds [c1,...,cn]) = R
       W = R, except that R is a regular expression 
       with non-empty contextblocks as leaves
    *)
    fun worldsToReg (T.Worlds nil) = One
      | worldsToReg (T.Worlds cids) = Star (worldsToReg' cids)
    and worldsToReg' (cid::nil) = Block (cid, I.constBlock cid)
      | worldsToReg' (cid::cids) =
          Plus (Block (cid, I.constBlock cid), worldsToReg' cids)

    (* init b (G, L) raises Success iff V is empty
       or none of the remaining declarations are relevant to b
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- L dlist, L nf
    *)
    fun init b (_, Vs as (I.Root _, s)) = 
        (Trace.success () ; 
	 raise Success (Whnf.normalize Vs))
      | init b (G, (V as I.Pi ((D1 as I.Dec (_, V1), _), V2), s)) =
(*        if Subordinate.belowEq (I.targetFam V1, b)
	  then *) (Trace.unmatched (G, subGoalToDList (Whnf.normalize (V, s))) ; ())
(*	else init b (decUName (G, D1), V2) *)

    (* accR ((G, (V, s)), R, k)   raises Success
       iff V[s] = {L1}{L2} P  such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- (V s) type, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    fun accR (GVs, One, b, k) = k GVs
      | accR (GVs as (G, (V, s)), Block (c, (someDecs, piDecs)), b, k) =
        let
	  val t = createEVarSub (G, someDecs) (* G |- t : someDecs *)
	  val _ = Trace.matchBlock ((G, subGoalToDList (Whnf.normalize (V, s))), Seq (1, piDecs, t))
 	  (* if block matches, check for remaining constraints *)
	  (* can there be uninstantiated variable left over? 
	     I suspect no.  If yes, something is underspecified 
	     Is this part of the invariant? --cs *)
	  val k' = (fn (G', Vs') => 
		    ((* print ("OK block identified: " ^ I.conDecName (I.sgnLookup c) ^ "\n");
		        --cs Sat Nov 15 09:20:36 2003 *)
		      if noConstraints (G, t)
		     then k (G', Vs')
		     else (Trace.constraintsRemain (); ())))
		       
	in
	  accR ((decUName (G, I.BDec (NONE, (c, t))), (V, I.comp (s, I.shift))), 
		Seq (1, piDecs, I.comp (t, I.shift)), b, k')
	  handle Success V => raise Success (Whnf.normalize (I.Pi ((I.BDec (NONE, (c, t)), I.Maybe), V), I.id))
	end
      | accR ((G, (V as I.Pi ((D as I.Dec (_, V1), _), V2), s)),
	      L' as Seq (j, I.Dec (_, V1')::L2', t), b, k) =
	if Unify.unifiable (G, (V1, s), (V1', t))
	  then accR ((G, (V2, I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), s))), 
		     Seq (j+1, L2', I.Dot (I.Exp (I.Root (I.Proj (I.Bidx 1, j), I.Nil)), t)), b, k)
	else  (Trace.mismatch (G, (V1, I.id), (V1', t)) ; ())  
          (* different from world checking, we do not allow skipping of assumptions here *)
      | accR (GVs, Seq (_, nil, t), b, k) = k GVs
      | accR (GVs as (G, (I.Root _, s)), R as Seq (_, L', t), b, k) =
	  ( Trace.missing (G, R); () )	(* L is missing *)
      | accR (GVs, Plus (r1, r2), b, k) =
	  ( CSManager.trail (fn () => accR (GVs, r1, b, k)) ;
	    accR (GVs, r2, b, k) )
      | accR (GVs, Star (One), b, k) = k GVs (* only possibility for non-termination in next rule *)
      | accR (GVs, r as Star(r'), b, k) = (* r' does not accept empty declaration list *)
	  ( CSManager.trail (fn () => k GVs) ;
	    accR (GVs, r', b, fn GVs' => accR (GVs', r, b, k)))


    (* worldifyBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise
  
       Invariants: G |- V : type, V nf
    *)
    fun worldifyBlocks (W as T.Worlds cids) (G, V, occ) = 
        let
	  val b = I.targetFam V
	  val _ = W.isSubsumed W b
	  val Wb = W.getWorlds b
	  val Rb = worldsToReg Wb
	in
	  (accR ((G, (V, I.id)), Rb, b, init b);
	   raise Error' (occ, "World violation"))
	end
	handle Success V' => V'

    (******************************)
    (* Worldifying clauses and goals *)
    (******************************)

    (* worldifyClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     fun worldifyClause (G, V as I.Root (a, S), W, occ) = V
       | worldifyClause (G, I.Pi ((D as I.Dec (x, V1), I.Maybe), V2), W, occ) = 
         let 
	   val W2 = worldifyClause (decEName (G, D), V2, W, P.body occ)
	   val W1 = worldifyGoal (G, V1, W, P.label occ)
	 in 
	   I.Pi ((I.Dec (x, W1), I.Maybe), W2)
	 end
       | worldifyClause (G, I.Pi ((D as I.Dec (x, V1), I.No), V2), W, occ) = 
	 let 
	   val W1 = worldifyBlocks W (G, V1, P.label occ)
	   val W2 = worldifyClause (decEName (G, D), V2, W, P.body occ);
     	   (* worldifyGoal (G, V1, W, P.label occ))  -- unnecessary?*)
	 in
	   I.Pi ((I.Dec (x, W1), I.No), W2)
	 end

     (* worldifyGoal (G, V, W, occ) = () 
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

	Invariant: G |- V : type, V nf
     *)
     (* Question: should dependent Pi's really be worldifyed recursively? *)
     (* Thu Mar 29 09:38:20 2001 -fp *)
     and worldifyGoal (G, V as I.Root (a, S), W, occ) = V
       | worldifyGoal (G, I.Pi ((D as I.Dec (x, V1), DP), V2), W, occ) =
         let 
	   val W2 = worldifyGoal (decUName (G, D), V2, W, P.body occ)
	   val W1 = worldifyClause (G, V1, W, P.label occ)
	 in
	   I.Pi ((I.Dec (x, W1), DP), V2)
	 end


     (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
     *)
     fun worldifyConDec W (c, I.ConDec (s, m, k, status, V, L)) = 
         (if !Global.chatter = 4
	    then print (Names.qidToString (Names.constQid c) ^ " ")
	  else ();
	    if !Global.chatter > 4 then Trace.clause c else ();
	      (I.ConDec (s, m, k, status, worldifyClause (I.Null, V, W, P.top), L))
	      handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg)))
       (* by invariant, other cases cannot apply *)

     fun worldify a =  
	 let
	   val W = W.lookup a
	   val _ = if !Global.chatter > 3
		     then print ("World checking family " ^ Names.qidToString (Names.constQid a) ^ ":\n")
		   else ()
(*	   val _ = subsumedReset ()	(* initialize table of subsumed families *)
*)	    
	   val condecs = map (fn (I.Const c) => worldifyConDec W (c, I.sgnLookup c)) 
	                     (Index.lookup a)

	   val _ = if !Global.chatter = 4 then print "\n" else ()
	 in
	   condecs
	 end


     fun check a = 
         let 
	   val condecs = worldify a
	 in 
	   ()
	 end
  in
    val worldify = worldify
    val worldifyGoal = fn (G,V) => worldifyGoal (G, V, W.lookup (I.targetFam V), P.top)
  end

end;  (* functor Worldify *)
