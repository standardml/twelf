(* World Checking *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor WorldSyn
  (structure Global : GLOBAL
   structure IntSyn : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn
   structure Unify : UNIFY
     sharing Unify.IntSyn = IntSyn
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn
   structure Constraints : CONSTRAINTS
     sharing Constraints.IntSyn = IntSyn
   structure CSManager : CS_MANAGER
     sharing CSManager.IntSyn = IntSyn
   structure Subordinate : SUBORDINATE
     sharing Subordinate.IntSyn = IntSyn
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn

   structure Table : TABLE where type key = int

   structure Paths : PATHS
   structure Origins : ORIGINS
     sharing Origins.Paths = Paths
     sharing Origins.IntSyn = IntSyn)
   : WORLDSYN = 
struct
  structure IntSyn = IntSyn
  structure I = IntSyn
  structure P = Paths
  structure F = Print.Formatter

  exception Error of string 

  exception Error' of P.occ * string

  (* copied from terminates/reduces.fun *)
  fun wrapMsg (c, occ, msg) =  
      (case Origins.originLookup c
	 of (fileName, NONE) => (fileName ^ ":" ^ msg)
          | (fileName, SOME occDec) => 
		(P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
			     Origins.linesInfoLookup (fileName),
			     "Constant " ^ Names.constName c ^ "\n" ^ msg)))

  type dlist = IntSyn.Dec list

  datatype LabelDec =			(* ContextBody                 *)
    LabelDec of string * dlist * dlist	(* B ::= l : SOME L1. BLOCK L2 *)

  datatype World =			(* Worlds                      *)
    Closed				(* W ::= .                     *)
  | Schema of World * LabelDec          (*     | W, B                  *)

  local
   
    val worldsTable : World Table.Table = Table.new (0)
    fun reset () = Table.clear worldsTable
    fun insert (cid, W) = Table.insert worldsTable (cid, W)
    fun getWorld (b) =
        (case Table.lookup worldsTable b
	   of NONE => raise Error ("Family " ^ Names.constName b ^ " has no worlds declaration")
            | SOME (Wb) => Wb)

    (* subsumedTable
       For each family a that is world-checked, this
       contains the subordinate families b whose worlds
       subsume that of a modulo subordination
    *)
    val subsumedTable : unit Table.Table = Table.new (0)
    fun subsumedReset () = Table.clear subsumedTable
    fun subsumedInsert (cid) = Table.insert subsumedTable (cid, ())
    fun subsumedLookup (cid) =
        (case Table.lookup subsumedTable cid
	   of NONE => false
            | SOME _ => true)

    (* Regular world expressions R
       Invariants:
       If R = (D1,...,Dn)[s] then G |- s : G' and G' |- D1,...,Dn ctx
       If R = r* then r = 1 or r does not accept the empty world
    *)
    datatype Reg			(* Regular world expressions  *)
      = Block of LabelDec		(* R ::= LD                   *)
      | Seq of dlist * I.Sub		(*     | (D1,...,Dn)[s]       *)
      | Star of Reg			(*     | R*                   *)
      | Plus of Reg * Reg		(*     | R1 + R2              *)
      | One				(*     | 1                    *)

    exception Success			(* signals worldcheck success *)

    (* createEVarSub G L = s
     
       Invariant:
       If   G is a context
       and  L is a context
       then G |- s : L
    *)
    fun createEVarSub (G, nil) = I.Shift (I.ctxLength G)
      | createEVarSub (G, (I.Dec (_, V) :: L)) = 
        let
	  val s = createEVarSub (G, L)
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
          formatD (G, D) :: nil (* Names.decUName (G, I.decSub(D, t)) *)
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
    fun wGoalToString ((G, L), Seq (piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, L, I.id)), F.Break,
				   F.String "<|", F.Break,
				   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    fun worldToString (G, Seq (piDecs, t)) =
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
          print ("World checking clause " ^ Names.constName c ^ "\n")
      fun constraintsRemain () =
	  if !Global.chatter > 4
	    then print ("Constraints remain after matching hypotheses against context block\n")
	  else ()
      fun matchBlock (GL, R) =		(* R = (D1,...,Dn)[t] *)
	  if !Global.chatter > 4
	    then print ("Matching:\n" ^ wGoalToString (GL, R) ^ "\n")
	  else ()
      fun unmatched GL =
	  if !Global.chatter > 4
	    then print ("Unmatched hypotheses:\n" ^ hypsToString GL ^ "\n")
	  else ()
      fun missing (G, R) =		(* R = (D1,...,Dn)[t] *)
	  if !Global.chatter > 4
	    then print ("Missing hypotheses:\n" ^ worldToString (G, R) ^ "\n")
	  else ()
      fun mismatch (G, Vs1, Vs2) =
	  if !Global.chatter > 4
	    then print ("Mismatch:\n" ^ mismatchToString (G, Vs1, Vs2) ^ "\n")
	  else ()
      fun success () =
	  if !Global.chatter > 4
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

    (* worldToReg W = R
  
       Invariant:
       W = R, except that R is a regular expression 
       with non-empty contextblocks as leaves
    *)
    fun worldToReg W = 
        let
	  fun worldToReg' (Closed) = One
	    | worldToReg' (Schema (Closed, L)) = Block L
	    | worldToReg' (Schema (W, L)) = Plus (worldToReg' W, Block L)
	in
	  Star (worldToReg' W)
	end

    (* init (G, V) raises Success iff V is atomic
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- V : type, V nf
    *)
    fun init (_, nil) = ( Trace.success () ; raise Success)
      | init (G, L) = ( Trace.unmatched (G, L) ; () )
      (* bug in line above: check subsumption!! *)

    (* accR ((G, L), R, k)   raises Success
       iff L = L1,L2 such that R accepts L1
           and k ((G, L1), L2) succeeds
       otherwise fails by returning ()
       Invariant: G |- L dlist, L nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    fun accR (GL, One, b, k) = k GL
      | accR (GL as (G, L), Block (LabelDec (_, someDecs, piDecs)), b, k) =
        let
	  val t = createEVarSub (G, someDecs) (* G |- t : someDecs *)
	  val _ = Trace.matchBlock (GL, Seq (piDecs, t))
 	  (* if block matches, check for remaining constraints *)
	  val k' = (fn GL' => if noConstraints (G, t)
				then k GL'
			      else ( Trace.constraintsRemain () ; () ))
	in
	  accR (GL, Seq (piDecs, t), b, k')
	end
      | accR ((G, L as (D as I.Dec (_, V1))::L2),
	      L' as Seq (I.Dec (_, V1')::L2', t), b, k) =
	if Subordinate.belowEq (I.targetFam V1, b)
	  then (* relevant to family b *)
	    if Unify.unifiable (G, (V1, I.id), (V1', t))
		 then accR ((decUName (G, D), L2), Seq (L2', I.dot1 t), b, k)
	       else ( Trace.mismatch (G, (V1, I.id), (V1', t)) ; () )
	else (* skip irrelevant declarations in L *)
	  accR ((decUName (G, D), L2), L', b, k)
      | accR (GL, Seq (nil, t), b, k) = k GL
      | accR (GL as (G, nil), R as Seq (L', t), b, k) =
	  ( Trace.missing (G, R); () )	(* L is missing *)
      | accR (GL, Plus (r1, r2), b, k) =
	  ( CSManager.trail (fn () => accR (GL, r1, b, k)) ;
	    accR (GL, r2, b, k) )
      | accR (GL, Star (One), b, k) = k GL (* only possibility for non-termination in next rule *)
      | accR (GL, r as Star(r'), b, k) = (* r' does not accept empty declaration list *)
	  ( CSManager.trail (fn () => k GL) ;
	    accR (GL, r', b, fn GL' => accR (GL', r, b, k)))

    (* checkSubsumedBlock (G, someDecs, piDecs, Rb, b) = ()
       iff block SOME someDecs. PI piDecs is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    fun checkSubsumedBlock (G, nil, L', Rb, b) =
        (( accR ((G, L'), Rb, b, init) ;
	  raise Error ("World subsumption failure for family " ^ Names.constName b) )
	 handle Success => ())
      | checkSubsumedBlock (G, D::L, L', Rb, b) =
	  checkSubsumedBlock (decEName (G, D), L, L', Rb, b)

    (* checkSubsumedWorlds (Wa, Rb, b) = ()
       iff Wa is subsumed by Rb
       Effect: raises Error (msg) otherwise

       Invariants: Rb = reg (worlds (b))
    *)
    fun checkSubsumedWorlds (Closed, Rb, b) = ()
      | checkSubsumedWorlds (Schema (Wa', LabelDec (_, someDecs, piDecs)), Rb, b) =
        ( checkSubsumedBlock (I.Null, someDecs, piDecs, Rb, b);
          checkSubsumedWorlds (Wa', Rb, b) )

    (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise
  
       Invariants: G |- V : type, V nf
    *)
    (* optimize: do not check atomic subgoals? *)
    fun checkBlocks Wa (G, V, occ) = 
        let
	  val b = I.targetFam V
	  val Wb = getWorld b handle Error (msg) => raise Error' (occ, msg)
	  val Rb = worldToReg Wb
	  val _ = if subsumedLookup b
		    then ()
		  else ( checkSubsumedWorlds (Wa, Rb, b) ;
			 subsumedInsert (b) )
	  val L = subGoalToDList V
	in
	  (accR ((G, L), Rb, b, init);
	   raise Error' (occ, "World violation"))
	end
	handle Success => ()

    (******************************)
    (* Checking clauses and goals *)
    (******************************)

    (* checkClause (G, V, W, occ) = ()
       iff all subgoals in V satisfy world spec W
       Effect: raises Error' (occ', msg) otherwise

       Invariant: G |- V : type, V nf
       occ is occurrence of V in current clause
     *)
     fun checkClause (G, I.Root (a, S), W, occ) = ()
       | checkClause (G, I.Pi ((D as I.Dec (_, V1), I.Maybe), V2), W, occ) = 
	 (checkClause (I.Decl (G, D), V2, W, P.body occ);
	  checkGoal (G, V1, W, P.label occ))
       | checkClause (G, I.Pi ((D as I.Dec (_, V1), I.No), V2), W, occ) = 
	 (checkBlocks W (G, V1, P.label occ);
	  checkClause (decEName (G, D), V2, W, P.body occ);
	  checkGoal (G, V1, W, P.label occ))

     (* checkGoal (G, V, W, occ) = () 
        iff all (embedded) subgoals in V satisfy world spec W
        Effect: raises Error' (occ', msg) otherwise

	Invariant: G |- V : type, V nf
     *)
     (* Question: should dependent Pi's really be checked recursively? *)
     (* Thu Mar 29 09:38:20 2001 -fp *)
     and checkGoal (G, I.Root (a, S), W, occ) = ()
       | checkGoal (G, I.Pi ((D as I.Dec (_, V1), _), V2), W, occ) =
	 (checkGoal (decUName (G, D), V2, W, P.body occ);
	  checkClause (G, V1, W, P.label occ))

    (* worldcheck W a = ()
       iff all subgoals in all clauses defining a satisfy world spec W
       Effect: raises Error(msg) otherwise, where msg includes location
    *)
    fun worldcheck W a =  
	let
	  val _ = if !Global.chatter > 3
		    then print ("World checking family " ^ Names.constName a ^ ":\n")
		  else ()
	  val _ = subsumedReset ()	(* initialize table of subsumed families *)
	  fun checkAll nil = ()
	    | checkAll (I.Const c :: clist) =
	      (if !Global.chatter = 4
		 then print (Names.constName c ^ " ")
	       else ();
	       if !Global.chatter > 4 then Trace.clause c else ();
	       checkClause (I.Null, I.constType c, W, P.top)
		 handle Error' (occ, msg) => raise Error (wrapMsg (c, occ, msg));
               checkAll clist)
	  val _ = checkAll (Index.lookup a)
	  val _ = if !Global.chatter = 4 then print "\n" else ()
      in
	()
      end

    (**************************)
    (* Checking Subordination *)
    (**************************)

    (*
       At present, worlds declarations must respect the
       current subordination relation in order to guarantee
       soundness.
    *)

    (* checkSubordBlock (G, L, L') = ()
       Effect: raises Error(msg) if subordination is not respected
               in context block SOME L. PI L'
       Invariants: G |- SOME L. PI L' block
    *)
    fun checkSubordBlock (G, D::L, L') =
          checkSubordBlock (I.Decl (G, D), L, L')
      | checkSubordBlock (G, nil, (D as I.Dec(_,V))::L') =
	  ( Subordinate.respectsN (G, V); (* is V nf?  Assume here: yes -fp *)
	    checkSubordBlock (I.Decl (G, D), nil, L') )
      | checkSubordBlock (G, nil, nil) = ()

    (* checkSubordWorlds (W) = ()
       Effect: raises Error(msg) if subordination is not respected
               in some context block in W
    *)
    fun checkSubordWorlds (Closed) = ()
      | checkSubordWorlds (Schema (W, LabelDec (_, someDecs, piDecs))) =
          ( checkSubordWorlds W ;
	    checkSubordBlock (I.Null, someDecs, piDecs) )

    (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W does not respect subordination
    *)
    fun install (a, W) =
        ( checkSubordWorlds W
	    handle Subordinate.Error (msg) => raise Error (msg) ;
	  insert (a, W) )

    (* ctxtolist G = L
      
       Invariant:
       G = L  (G is left associative, L is right associative)
    *)
    fun ctxToList (Gin) = 
	let
	  fun ctxToList' (I.Null, G ) = G
	    | ctxToList' (I.Decl (G, D), G') =
	    ctxToList' (G, D :: G')
	in
	  ctxToList' (Gin, nil)
	end

  in
    val reset = reset
    val install = install
    val worldcheck = worldcheck
    val ctxToList = ctxToList
  end

end;  (* functor WorldSyn *)
