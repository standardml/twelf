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
    fun lookup (cid) = Table.lookup worldsTable (cid)
    
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

    fun hypsToDList (I.Root _) = nil
      | hypsToDList (I.Pi ((D, _), V)) =
          D::hypsToDList V

    (* Hypotheses and declaration lists *)
    fun wGoalToString ((G, V), Seq (piDecs, t)) =
        F.makestring_fmt (F.HVbox [F.HVbox (formatDList (G, hypsToDList V, I.id)), F.Break,
				   F.String "<|", F.Break,
				   F.HVbox (formatDList (G, piDecs, t))])

    (* Declaration list *)
    fun worldToString (G, Seq (piDecs, t)) =
          F.makestring_fmt (F.HVbox (formatDList (G, piDecs, t)))

    (* Hypotheses *)
    fun hypsToString (G, V) =
          F.makestring_fmt (F.HVbox (formatDList (G, hypsToDList V, I.id)))

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
      val matchBlock : (I.dctx * I.Exp) * Reg -> unit
      val unmatched : I.dctx * I.Exp -> unit
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
      fun matchBlock (GV, R) =		(* R = (D1,...,Dn)[t] *)
	  if !Global.chatter > 4
	    then print ("Matching:\n" ^ wGoalToString (GV, R) ^ "\n")
	  else ()
      fun unmatched (G, V) =
	  if !Global.chatter > 4
	    then print ("Unmatched hypotheses:\n" ^ hypsToString (G, V) ^ "\n")
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

    (* init (G, V) raises Success iff V is atomic
       otherwise fails by returning ()
       Initial continuation for world checker

       Invariant: G |- V : type, V nf
    *)
    fun init (_, I.Root _) = ( Trace.success () ; raise Success)
      | init (G, V) = ( Trace.unmatched (G, V) ; () )

    (* accR ((G, V), R, k)   raises Success
       iff V = {{G'}}V' such that R accepts {{G'}}
           and k ((G,G'), V') succeeds
       otherwise fails by returning ()
       Invariant: G |- V : type, V nf
                  R regular world expression
       trails at choice points to undo EVar instantiations during matching
    *)
    fun accR (GV, One, k) = k GV
      | accR (GV as (G, V), Block (LabelDec (_, someDecs, piDecs)), k) =
        let
	  val t = createEVarSub (G, someDecs) (* G |- t : someDecs *)
	  val _ = Trace.matchBlock (GV, Seq (piDecs, t))
 	  (* if block matches, check for remaining constraints *)
	  val k' = (fn GV' => if noConstraints (G, t)
				then k GV'
			      else ( Trace.constraintsRemain () ; () ))
	in
	  accR (GV, Seq (piDecs, t), k')
	end
      | accR ((G, V as I.Pi ((D as I.Dec (_, V1), _), V2)),
	      Seq (I.Dec (_, V1')::L2, t), k) =
	if Unify.unifiable (G, (V1, I.id), (V1', t))
	  then accR ((decUName (G, D), V2), Seq (L2, I.dot1 t), k)
	else ( Trace.mismatch (G, (V1, I.id), (V1', t)) ; () )
      | accR (GV, Seq (nil, t), k) = k GV
      | accR (GV as (G, I.Root _), R as Seq (L, t), k) =
	  ( Trace.missing (G, R); () )	(* L is missing *)
      | accR (GV, Plus (r1, r2), k) =
	  ( CSManager.trail (fn () => accR (GV, r1, k)) ;
	    accR (GV, r2, k) )
      | accR (GV, Star (One), k) = k GV	(* only possibility for non-termination in next rule *)
      | accR (GV, r as Star(r'), k) =	(* r' does not accept empty declaration list *)
	  ( CSManager.trail (fn () => k GV) ;
	    accR (GV, r', fn GV' => accR (GV', r, k)))

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

    (* checkBlocks W (G, V, occ) = ()
       iff V = {{G'}} a @ S and G' satisfies worlds W
       Effect: raises Error'(occ, msg) otherwise
  
       Invariants: G |- V : type, V nf
    *)
    (* optimize: do not check atomic subgoals? *)
    fun checkBlocks W (G, V, occ) = 
        (accR ((G, V), worldToReg W, init);
	 raise Error' (occ, "World violation"))
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
     and checkGoal (G, I.Root (a, S), W, occ) = ()
       | checkGoal (G, I.Pi ((D as I.Dec (_, V1), _), V2), W, occ) =
	   (checkGoal (decUName (G, D), V2, W, P.body occ) ;
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

    (* Checking that worlds declaration respects the subordination that is present *)

    fun checkSubordBlock (G, D::L, L') =
          checkSubordBlock (I.Decl (G, D), L, L')
      | checkSubordBlock (G, nil, (D as I.Dec(_,V))::L') =
	  ( Subordinate.respectsN (G, V); (* is V nf?  Assume here: yes -fp *)
	    checkSubordBlock (I.Decl (G, D), nil, L') )
      | checkSubordBlock (G, nil, nil) = ()

    fun checkSubordWorlds (Closed) = ()
      | checkSubordWorlds (Schema (W, LabelDec (_, someDecs, piDecs))) =
          ( checkSubordWorlds W ;
	    checkSubordBlock (I.Null, someDecs, piDecs) )

    (* install (a, W) = ()
       install worlds declaration W for family a

       Effect: raises Error if W would change subordination
    *)
    fun install (a, W) =
        ( checkSubordWorlds W
	    handle Subordinate.Error (msg) => raise Error (msg) ;
	  insert (a, W) )

  in
    val reset = reset
    val install = install
    val worldcheck = worldcheck
    val ctxToList = ctxToList
  end

end;  (* functor WorldSyn *)
