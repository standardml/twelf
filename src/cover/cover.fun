(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure Unify : UNIFY		(* must be trailing! *)
     sharing Unify.IntSyn = IntSyn'
   structure Constraints : CONSTRAINTS
     sharing Constraints.IntSyn = IntSyn'
   structure ModeSyn' : MODESYN
     sharing ModeSyn'.IntSyn = IntSyn'
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Paths : PATHS
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn'
   structure CSManager : CS_MANAGER
     sharing CSManager.IntSyn = IntSyn')
  : COVER =
struct
  structure IntSyn = IntSyn'
  structure ModeSyn = ModeSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure P = Paths
    structure F = Print.Formatter

    (*
       Coverage goals have the form {{G}} a @ S
    *)

    (******************************************)
    (*** Creating the Initial Coverage Goal ***)
    (******************************************)

    (* buildSpine n = n; n-1; ...; 1; Nil *)

    fun buildSpine 0 = I.Nil
      | buildSpine n = (* n > 0 *)
        I.App (I.Root (I.BVar(n), I.Nil), buildSpine (n-1))

    (* initCGoal' (a, k, G, V) = {x1:V1}...{xn:Vn} a x1...xn

       Invariants (modulo some renaming):
       |- a : {x1:V1}...{xn:Vn} type
       G = {x1:V1}...{xk:Vk}
       V = {xk+1:Vk+1}...{xn:Vn} type 
       G |- V : type
    *)
    fun initCGoal' (a, k, G, I.Pi ((D, P), V)) =
        let
	  val D' = Names.decEName (G, D)
	in
          I.Pi ((D', I.Maybe), initCGoal' (a, k+1, I.Decl (G, D'), V))
	end
      | initCGoal' (a, k, G, I.Uni (I.Type)) =
          I.Root (a, buildSpine k)

    (* initCGoal (a) = {x1:V1}...{xn:Vn} a x1...xn
       where a : {x1:V1}...{xn:Vn} type
    *)
    fun initCGoal (a) = initCGoal' (I.Const (a), 0, I.Null, I.constType (a))

    (***********************************************)
    (*** Matching Coverage Goals against Clauses ***)
    (***********************************************)

    (* Equation G |- (U1,s1) = (U2,s2)
       Invariant: 
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V

       U1[s1] has no EVars (part of coverage goal)
    *)
    datatype Equation = Eqn of I.dctx * I.eclo * I.eclo

    (* Splitting candidates *)
    (* Splitting candidates [k1,...,kl] are indices
       into coverage goal {xn:Vn}...{x1:V1} a M1...Mm, counting right-to-left
    *)
    datatype Candidates =
        Eqns of Equation list		(* equations to be solved, everything matches so far *)
      | Cands of int list		(* candidates for splitting, matching fails *)
      | Fail				(* coverage fails without candidates *)

    (* fail () = Fail
       indicate failure without splitting candidates
     *)
    fun fail () = Fail

    (* failAdd (k, cands) = cands'
       indicate failure, but add k as splitting candidate
    *)
    fun failAdd (k, Eqns _) = Cands (k::nil) (* no longer matches *)
      | failAdd (k, Cands (ks)) = Cands (k::ks) (* remove duplicates? *)
      | failAdd (k, Fail) = Fail

    (* addEqn (e, cands) = cands'
       indicate possible match if equation e can be solved
    *)
    fun addEqn (e, Eqns (es)) = Eqns (e::es) (* still may match: add equation *)
      | addEqn (e, cands as Cands (ks)) = (* already failed: ignore new constraints *)
          cands
      | addEqn (e, Fail) = Fail		(* already failed without candidates *)

    (* matchEqns (es) = true 
       iff  all equations in es can be simultaneously unified

       Effect: instantiate EVars right-hand sides of equations.
    *)
    fun matchEqns (nil) = true
      | matchEqns (Eqn (G, Us1, Us2)::es) =
        Unify.unifiable (G, Us1, Us2)
	andalso matchEqns (es)

    (* resolveCands (cands) = cands'
       resolve to one of
	 Eqns(nil) - match successful
	 Fail      - no match, no candidates
	 Cands(ks) - candidates ks
       Effect: instantiate EVars in right-hand sides of equations.
    *)
    fun resolveCands (Eqns (es)) =
        if matchEqns (es) then (Eqns (nil))
	else Fail
      | resolveCands (Cands (ks)) = Cands (ks)
      | resolveCands (Fail) = Fail

    (* collectConstraints (Xs) = constrs
       collect all the constraints that may be attached to EVars Xs

       try simplifying away the constraints in case they are "hard"
       disabled for now to get a truer approximation to operational semantics
    *)
    fun collectConstraints (nil) = nil
      | collectConstraints (I.EVar (_, _, _, ref nil)::Xs) =
          collectConstraints Xs
      | collectConstraints (I.EVar (_, _, _, ref constrs)::Xs) =
	  (* constrs <> nil *)
          (* Constraints.simplify constrs @ *) (* at present, do not simplify -fp *)
	  constrs @ collectConstraints Xs

    (* checkConstraints (cands, (Q, s)) = cands'
       failure if constraints remain in Q[s] which indicates only partial match
       Q[s] is the clause head after matching the coverage goal.

       Invariants: if cands = Eqns (es) then es = nil.
    *)
    fun checkConstraints (G, Qs, Cands (ks)) = Cands (ks)
      | checkConstraints (G, Qs, Fail) = Fail
      | checkConstraints (G, Qs, Eqns _) = (* _ = nil *)
        let
	  val Xs = Abstract.collectEVars (G, Qs, nil)
	  val constrs = collectConstraints Xs
	in
	  case constrs
	    of nil => Eqns (nil)
	     | _ => Fail		(* constraints remained: Fail without candidates *)
	end

    (* Candidate Lists *)
    (*
       Candidate lists record constructors and candidates for each
       constructors or indicate that the coverage goal is matched.
    *)
    datatype CandList =
        Covered				(* covered---no candidates *)
      | CandList of Candidates list     (* cands1,..., candsn *)

    (* addKs (cands, klist) = klist'
       add new constructor to candidate list
    *)
    fun addKs (ccs as Cands(ks), CandList (klist)) = CandList (ccs::klist)
      | addKs (ces as Eqns(nil), CandList (klist)) = Covered
      | addKs (cfl as Fail, CandList (klist)) = CandList (cfl::klist)

    (* matchExp (G, d, (U1, s1), (U2, s2), cands) = cands'
       matches U1[s1] (part of coverage goal)
       against U2[s2] (part of clause head)
       adds new candidates to cands to return cands'
         this could collapse to Fail,
         postponed equations Eqns(es),
         or candidates Cands(ks)
       d is depth, k <= d means local variable, k > d means coverage variable

       Invariants:
       G |- U1[s1] : V
       G |- U2[s2] : V  for some V
       G = Gc, Gl where d = |Gl|
    *)
    fun matchExp (G, d, Us1, Us2, cands) =
        matchExpW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, cands)

    and matchExpW (G, d, Us1 as (I.Root (H1, S1), s1), Us2 as (I.Root (H2, S2), s2), cands) =
        (case (H1, H2)
	   (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (k1), I.BVar(k2)) =>
	      if (k1 = k2)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else if k1 > d
		     then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
		   else fail ()		(* otherwise fail with no candidates *)
	    | (I.Const(c1), I.Const(c2)) =>
	      if (c1 = c2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else fail ()		(* fail with no candidates *)
            | (I.Def (d1), I.Def (d2)) =>
	      if (d1 = d2)		(* because of strictness *)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else matchExpW (G, d, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
	    | (I.Def (d1), _) => matchExpW (G, d, Whnf.expandDef Us1, Us2, cands)
	    | (_, I.Def (d2)) => matchExpW (G, d, Us1, Whnf.expandDef Us2, cands)
	    | (I.BVar (k1), I.Const _) =>
	      if k1 > d
		then failAdd (k1-d, cands) (* k1 is coverage variable, new candidate *)
	      else fail ()		(* otherwise fail with no candidates *)
	    | (I.Const _, I.BVar _) => fail ()
            (* no other cases should be possible *)
	    )
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (I.Lam (D2, U2), s2), cands) =
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1, (U1, I.dot1 s1), (U2, I.dot1 s2), cands)
      | matchExpW (G, d, (I.Lam (D1, U1), s1), (U2, s2), cands) =
	   (* eta-expand *)
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1,
		     (U1, I.dot1 s1),
		     (I.Redex (I.EClo (U2, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s2),
		     cands)
      | matchExpW (G, d, (U1, s1), (I.Lam (D2, U2), s2), cands) =
	   (* eta-expand *)
	   matchExp (I.Decl (G, I.decSub (D2, s2)), d+1,
		     (I.Redex (I.EClo (U1, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s1),
		     (U2, I.dot1 s2),
		     cands)
      | matchExpW (G, d, Us1, Us2 as (I.EVar _, s2), cands) =
	   addEqn (Eqn (G, Us1, Us2), cands)
      (* nothing else should be possible, by invariants *)
      (* No I.Uni, I.Pi, I.FgnExp, and no I.Redex by whnf *)

    and matchSpine (G, d, (I.Nil, _), (I.Nil, _), cands) = cands
      | matchSpine (G, d, (I.SClo (S1, s1'), s1), Ss2, cands) =
          matchSpine (G, d, (S1, I.comp (s1', s1)), Ss2, cands)
      | matchSpine (G, d, Ss1, (I.SClo (S2, s2'), s2), cands) =
	  matchSpine (G, d, Ss1, (S2, I.comp (s2', s2)), cands)
      | matchSpine (G, d, (I.App (U1, S1), s1), (I.App (U2, S2), s2), cands) =
	let
	  val cands' = matchExp (G, d, (U1, s1), (U2, s2), cands)
	in
	  matchSpine (G, d, (S1, s1), (S2, s2), cands')
	end

    (* matchTop (G, (a @ S1, s1), (a @ S2, s2), ms) = cands
       matches S1[s1] (spine of coverage goal)
       against S2[s2] (spine of clause head)
       skipping over `ignore' ( * ) or `output' ( - ) argument in mode spine ms

       Invariants:
       G |- a @ S1[s1] : type
       G |- a @ S2[s2] : type
       G contains coverage variables,
       S1[s1] contains no EVars
       mode spine ms matches S1 and S2
    *)
    fun matchTop (G, Us1, Us2, ms) =
          matchTopW (G, Whnf.whnf Us1, Whnf.whnf Us2, ms)
    and matchTopW (G, (I.Root (_, S1), s1), (I.Root (_, S2), s2), ms) =
        (* heads must be equal by invariant *)
        (* unify spines, skipping output and ignore arguments in modeSpine *)
          matchTopSpine (G, (S1, s1), (S2, s2), ms, Eqns (nil))
    and matchTopSpine (G, (I.Nil, _), (I.Nil, _), M.Mnil, cands) = cands
      | matchTopSpine (G, (I.SClo (S1, s1'), s1), Ss2, ms, cands) =
          matchTopSpine (G, (S1, I.comp (s1', s1)), Ss2, ms, cands)
      | matchTopSpine (G, Ss1, (I.SClo (S2, s2'), s2), ms, cands) =
          matchTopSpine (G, Ss1, (S2, I.comp (s2', s2)), ms, cands)
      | matchTopSpine (G, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
		       M.Mapp (M.Marg (M.Plus, _), ms'), cands) =
        let
	  val cands' = matchExp (G, 0, (U1, s1), (U2, s2), cands)
	in
	   matchTopSpine (G, (S1, s1), (S2, s2), ms', cands')
	end
      | matchTopSpine (G, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
		       M.Mapp (_, ms'), cands) =
	(* skip "ignore" and "output" arguments *)
	   matchTopSpine (G, (S1, s1), (S2, s2), ms', cands)

    (* matchClause (G, (a @ S1, s1), V, ms) = cands
       as in matchTop, but r is compiled clause
       NOTE: Simply use constant type for more robustness (see below)
    *)
    fun matchClause (G, ps', qs as (I.Root (_, _), s), ms) =
          checkConstraints (G, qs, resolveCands (matchTop (G, ps', qs, ms)))
      | matchClause (G, ps', (I.Pi ((I.Dec(_, V1), _), V2), s), ms) =
        let
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s))
	in
	  matchClause (G, ps', (V2, I.Dot (I.Exp (X1), s)), ms)
	end

    (* matchSig (G, (a @ S, s), ccs, ms, klist) = klist'
       match coverage goal {{G}} a @ S[s]
       against each coverage clause V in ccs,
       adding one new list cand for each V to klist to obtain klist'

       Invariants:
       G |- a @ S[s] : type
       V consists of clauses with target type a @ S'
       ms matches S
       klist <> Covered
    *)
    fun matchSig (G, ps', nil, ms, klist) = klist
      | matchSig (G, ps', V::ccs', ms, klist) =
        let
	  val cands = CSManager.trail
	              (fn () => matchClause (G, ps', (V, I.id), ms))
	in
	  matchSig' (G, ps', ccs', ms, addKs (cands, klist))
	end

    (* matchSig' (G, (a @ S, s), ccs, ms, klist) = klist'
       as matchSig, but check if coverage goal {{G}} a @ S[s] is already matched
    *)
    and matchSig' (G, ps', ccs, ms, Covered) = Covered (* already covered: return *)
      | matchSig' (G, ps', ccs, ms, CandList (klist)) = (* not yet covered: continue to search *)
          matchSig (G, ps', ccs, ms, CandList (klist))

    (* match (G, V, ms, ccs) = klist
       matching coverage goal {{G}} V against coverage clauses Vi in ccs
       yields candidates klist
       no local assumptions
       Invariants:
       V = {xk+1:Vk+1}...{xn:Vn} a @ S
       G = {x1:V1}...{xk:Vk}
       mode spine ms matches S
       G |- V : type
    *)
    fun match (G, V as I.Root (I.Const (a), S), ms, ccs) =
          matchSig (G, (V, I.id), ccs, ms, CandList (nil))
      | match (G, I.Pi ((D, _), V'), ms, ccs) =
	  match (I.Decl (G, D), V', ms, ccs)

    (************************************)
    (*** Selecting Splitting Variable ***)
    (************************************)

    (* insert (k, ksn) = ksn'
       ksn is ordered list of ks (smallest index first) with multiplicities
    *)
    fun insert (k, nil) = ((k, 1)::nil)
      | insert (k, ksn as (k', n')::ksn') =
        (case Int.compare (k, k')
	   of LESS => (k, 1)::ksn
	    | EQUAL => (k', n'+1)::ksn'
	    | GREATER => (k', n')::insert (k, ksn'))

    (* join (ks, ksn) = ksn'
       ksn is as in function insert
    *)
    fun join (nil, ksn) = ksn
      | join (k::ks, ksn) = join (ks, insert (k, ksn))

    (* selectCand (klist) = ksnOpt
       where ksOpt is an indication of coverage (NONE)
       or a list of candidates with multiplicities

       Simple heuristic: select last splitting candidate from last clause tried
       This will never pick an index variable unless necessary.
    *)
    fun selectCand (Covered) = NONE	(* success: case is covered! *)
      | selectCand (CandList (klist)) = selectCand' (klist, nil)

    and selectCand' (nil, ksn) = SOME(ksn) (* failure: case G,V is not covered! *)
      | selectCand' (Fail::klist, ksn) = (* local failure (clash) and no candidates *)
          selectCand' (klist, ksn)
      | selectCand' (Cands(nil)::klist, ksn) = (* local failure but no candidates *)
	  selectCand' (klist, ksn)
      | selectCand' (Cands(ks)::klist, ksn) = (* found candidates ks <> nil *)
	  selectCand' (klist, join (ks, ksn))

    (*****************)
    (*** Splitting ***)
    (*****************)

    (*
       In a coverage goal {{G}} a @ S we instantiate each
       declaration in G with a new EVar, then split one of these variables,
       then abstract to obtain a new coverage goal {{G'}} a @ S'
    *)

    (* instEVars ({xn:Vn}...{x1:Vn} a @ S) = (a @ S[s], [X1,...,Xn])
       where . |- s : {xn:Vn}...{x1:V1}
       and s = X1...Xn.id, all Xi are new EVars
    *)       
    fun instEVars (Vs, XsRev) = instEVarsW (Whnf.whnf Vs, XsRev)
    and instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), XsRev) =
        let
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
	in
	  instEVars ((V2, I.Dot (I.Exp (X1), s)), X1::XsRev)
	end
      | instEVarsW (Vs as (I.Root _, s), XsRev) = (Vs, XsRev)

    (* caseList is a list of possibilities for a variables
       to be split.  Maintained as a mutable reference so it
       can be updated in the success continuation.
    *)
    local 
      val caseList : I.Exp list ref = ref nil
    in
      fun resetCases () = (caseList := nil)
      fun addCase (V) = (caseList := V :: !caseList)
      fun getCases () = (!caseList)
    end

    (* next section adapted from m2/metasyn.fun *)

    (* createEVarSpineW (G, (V, s)) = ((V', s') , S')

       Invariant:
       If   G |- s : G1   and  G1 |- V = Pi {V1 .. Vn}. W : L
       and  G1, V1 .. Vn |- W atomic  
       then G |- s' : G2  and  G2 |- V' : L
       and  S = X1; ...; Xn; Nil
       and  G |- W [1.2...n. s o ^n] = V' [s']
       and  G |- S : V [s] >  V' [s']
    *)
    fun createEVarSpine (G, Vs) = createEVarSpineW (G, Whnf.whnf Vs)
    and createEVarSpineW (G, Vs as (I.Root _, s)) = (I.Nil, Vs)   (* s = id *)
      | createEVarSpineW (G, (I.Pi ((D as I.Dec (_, V1), _), V2), s)) =  
	let 
	  val X = I.newEVar (G, I.EClo (V1, s))
	  val (S, Vs) = createEVarSpine (G, (V2, I.Dot (I.Exp (X), s)))
	in
	  (I.App (X, S), Vs)
	end
      (* Uni or other cases should be impossible *)
      (* mod: m2/metasyn.fun allows Uni(Type) *)

    (* createAtomConst (G, c) = (U', (V', s'))

       Invariant: 
       If   S |- c : Pi {V1 .. Vn}. V 
       then . |- U' = c @ (X1; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomConst (G, H as I.Const (cid)) = 
        let
	  val V = I.constType cid
	  val (S, Vs) = createEVarSpine (G, (V, I.id))
	in
	  (I.Root (H, S), Vs)
	end
        (* mod: m2/metasyn.fun allows skolem constants *)

    (* createAtomBVar (G, k) = (U', (V', s'))

       Invariant: 
       If   G |- k : Pi {V1 .. Vn}. V 
       then . |- U' = k @ (Xn; .. Xn; Nil)
       and  . |- U' : V' [s']
    *)
    fun createAtomBVar (G, k) =
	let
	  val I.Dec (_, V) = I.ctxDec (G, k)
	  val (S, Vs) = createEVarSpine (G, (V, I.id))
	in
	  (I.Root (I.BVar (k), S), Vs)
	end

    (* end m2/metasyn.fun *)

    (* next section adapted from m2/splitting.fun *)
    (* mod: success continuation with effect instead of abstraction function *)

    fun constCases (G, Vs, nil, sc) = ()
      | constCases (G, Vs, I.Const(c)::sgn', sc) =
        let
	  val (U, Vs') = createAtomConst (G, I.Const c)
	  val _ = CSManager.trail (fn () =>
				   if Unify.unifiable (G, Vs, Vs')
				     then sc U
				   else ())
	in
	  constCases (G, Vs, sgn', sc)
	end

    fun paramCases (G, Vs, 0, sc) = ()
      | paramCases (G, Vs, k, sc) =
        let
	  val (U, Vs') = createAtomBVar (G, k)
	  val _ = CSManager.trail (fn () =>
				   if Unify.unifiable (G, Vs, Vs')
				     then sc U
				   else ())
	in
	  paramCases (G, Vs, k-1, sc)
	end

    fun lowerSplit (G, Vs, sc) = lowerSplitW (G, Whnf.whnf Vs, sc)
    and lowerSplitW (G, Vs as (I.Root (I.Const a, _), s), sc) =
        let
	  val _ = constCases (G, Vs, Index.lookup a, sc) (* will trail *)
	  val _ = paramCases (G, Vs, I.ctxLength G, sc)	(* will trail *)
	in
	  ()
	end
      | lowerSplitW (G, (I.Pi ((D, P), V), s), sc) =
	let
	  val D' = I.decSub (D, s)
	in
	  lowerSplit (I.Decl (G, D'), (V, I.dot1 s), fn U => sc (I.Lam (D', U)))
	end

    (* end m2/splitting.fun *)


    (* splitEVar X sc = ()  --- call sc on all cases for X *)

    fun splitEVar ((X as I.EVar (_, GX, V, _)), sc) = (* GX = I.Null *)
          lowerSplit (I.Null, (V, I.id),
		      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id)) (* always succeeds? *)
				then sc ()
			      else ())

    (* abstract (a @ S, s) = V'
       where V' = {{G}} a @ S' and G abstracts over all EVars in a @ S[s]
       in arbitrary order

       Invariants: . |- a @ S[s] : type
       Effect: may raise Constraints.Error (constrs)
     *)
    fun abstract (V, s) = 
        let
	  val (i, V') = Abstract.abstractDecImp (I.EClo (V, s))
	in
	  V'
	end

    (* splitVar ({{G}} a @ S, k) = SOME [{{G1}} a @ S1 ,..., {{Gn}} a @ Sn]
       or NONE
       where {{Gi}} a @ Si are new coverage goals obtained by
       splitting kth variable in G, counting right-to-left.
       returns NONE if splitting variable k fails because of constraints

       Invariants: G |- a @ S : type, k <= |G|
       {{Gi}} a @ Si cover {{G}} a @ S
    *)
    fun splitVar (V, k) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), nil)
          (* split on k'th variable, counting from innermost *)
	  val X = List.nth (XsRev, k-1)
	  val _ = resetCases ()
	  val _ = splitEVar (X, fn () => addCase (abstract (V1, s)))
	in
	  SOME (getCases ())
	end
        (* Constraints.Error could be raise by abstract *)
        handle Constraints.Error (constrs) => NONE

    (*********************************)
    (* Checking for Impossible Cases *)
    (*********************************)

    exception Possible

    (* impossible1 X = true
       iff there is no constructor for EVar X
    *)
    fun impossible1 (X) =
        (* raised exception bypasses trail manager *)
        (* trail here explicitly because of dependencies *)
        CSManager.trail
	(fn () => (splitEVar (X, fn () => raise Possible); true) (* impossible, if returns *)
	          handle Possible => false)

    (* impossibleCase (Xs) = true
       iff there is no constructor for one of the variables among EVars Xs
    *)
    fun impossibleCase (nil) = false	(* no impossible coverage variable found *)
      | impossibleCase (X::Xs) =
          impossible1 X orelse impossibleCase Xs

    (* impossible {{G}} a @ S = true
       iff the coverage goal {{G}} a @ S is satisfied because one of
       the coverage variables in G has no constructor
       Invariants: G |- a @ S : type
    *)
    fun impossible (V) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), nil)
	in
	  impossibleCase (XsRev)
	end

    (***************************)
    (* Printing Coverage Goals *)
    (***************************)

    (* we pass in the mode spine specifying coverage, but currently ignore it *)
    fun abbrevCSpine (S, ms) = S

    fun abbrevCGoal (G, I.Pi((D, P), V), ms) =
        let 
	  val D' = Names.decEName (G, D)
	in
	  I.Pi ((D', P), abbrevCGoal (I.Decl (G, D'), V, ms))
	end
      | abbrevCGoal (G, I.Root (a, S), ms) =
	I.Root (a, abbrevCSpine (S, ms))

    fun formatCGoal (V, ms) =
        let
	  val _ = Names.varReset I.Null
	in
	  Print.formatExp (I.Null, abbrevCGoal (I.Null, V, ms))
	end

    fun formatCGoals (V::nil, ms) = [formatCGoal (V, ms)]
      | formatCGoals (V::Vs, ms) =
          formatCGoal (V, ms) :: F.String "," :: F.Break :: formatCGoals (Vs, ms)

    fun missingToString (Vs, ms) =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (formatCGoals (Vs, ms)), F.String "."])

    (*********************)
    (* Coverage Checking *)
    (*********************)

    (* need to improve tracing with higher chatter levels *)
    (* ccs = covering clauses *)

    (* cover (V, ms, ccs, missing) = missing'
       covers ([V1,...,Vi], ms, ccs, missing) = missing'

       check if input (+) arguments in V or all Vi, respectively,
       are covered by clauses ccs, adding omitted cases
       to missing to yield missing'.
       ms is mode spine designating input arguments (+)
    *)
    fun cover (V, ms, ccs, missing) =
          split (V, selectCand (match (I.Null, V, ms, ccs)), ms, ccs, missing)

    and split (V, NONE, ms, ccs, missing) = 
        (* V is covered: return missing patterns from other cases *)
          missing
      | split (V, SOME(nil), ms, ccs, missing) =
        (* no candidates: check if coverage goal is impossible *)
        if impossible(V)		
	  then missing
	else V::missing
      | split (V, SOME((k,_)::ksn), ms, ccs, missing) =
	(* some candidates: split first, ignoring multiplicities *)
	(case splitVar (V, k)
	   of SOME(cases) => covers (cases, ms, ccs, missing)
	    | NONE => (* splitting variable k generated constraints *)
	      split (V, SOME (ksn), ms, ccs, missing)) (* try other candidates *)

    and covers (nil, ms, ccs, missing) = missing
      | covers (V::cases', ms, ccs, missing) =
          covers (cases', ms, ccs, cover (V, ms, ccs, missing))

    (******************)
    (* Input Coverage *)
    (******************)

    (* constsToTypes [c1,...,cn] = [V1,...,Vn] where ci:Vi.
       Generates coverage clauses from signature.
    *)
    fun constsToTypes (nil) = nil
      | constsToTypes (I.Const(c)::cs') = I.constType(c)::constsToTypes(cs')

    (*******************)
    (* Output Coverage *)
    (*******************)

    (* negateMode ms = ms'
       replaces mode + by -, - by +.
       Used for output coverage, where "ignore" ( * ) should be impossible.
    *)
    fun negateMode (M.Mnil) = M.Mnil
      | negateMode (M.Mapp (M.Marg (M.Plus, x), ms')) =
           M.Mapp (M.Marg (M.Minus, x), negateMode ms')
      | negateMode (M.Mapp (M.Marg (M.Minus, x), ms')) =
           M.Mapp (M.Marg (M.Plus, x), negateMode ms')
      (* M.Star impossible *)

    (* createCoverClause (G, V) = {{G}} V
       where {{G}} V is in NF
    *)
    fun createCoverClause (I.Decl (G, D), V) =
          createCoverClause (G, (I.Pi ((D, I.Maybe), V)))
      | createCoverClause (I.Null, V) =
	  Whnf.normalize (V, I.id)

    (* createCoverGoal (({{G}} a @ S, s), ms) = V'
       createCoverSpine ((S, s), (V, s'), ms) = S'

       where all variables in G are replaced by EVars
       and output arguments in S are replaced by new EVars

       Invariants: . |- ({{G}} a @ S)[s] : type
                   ms matches S
		   . |- V[s'] : type and (V,s) whnf

       Could probably be done more efficiently.
    *)
    fun createCoverGoal (Vs, ms) =
           createCoverGoalW (Whnf.whnf (Vs), ms)
    and createCoverGoalW ((I.Pi ((D as I.Dec (_, V1), _), V2), s), ms) =
        let
	  val X = I.newEVar (I.Null, I.EClo (V1, s))
	in
	  createCoverGoalW ((V2, I.Dot (I.Exp (X), s)), ms)
	end
      | createCoverGoalW ((I.Root (a as I.Const(cid), S), s), ms) = (* s = id *)
	I.Root (a, createCoverSpine ((S, s), (I.constType (cid), I.id), ms))

    and createCoverSpine ((I.Nil, s), _, M.Mnil) = I.Nil
      | createCoverSpine ((I.App (U1, S2), s), (I.Pi ((I.Dec (_, V1), _), V2), s'),
			  M.Mapp (M.Marg (M.Minus, x), ms')) =
          (* replace output argument by new variable *)
        let
	  val X = I.newEVar (I.Null, I.EClo (V1, s'))
	  val S2' = createCoverSpine ((S2, s), (V2, I.Dot (I.Exp (X), s')), ms')
	in
          I.App (X, S2')
	end
      | createCoverSpine ((I.App (U1, S2), s), (I.Pi (_, V2), s'), M.Mapp (_, ms')) =
	(* leave input or ignore arguments as they are *)
	  I.App (I.EClo (U1, s),
		 createCoverSpine ((S2, s), Whnf.whnf (V2, I.Dot (I.Exp (I.EClo (U1, s)), s')), ms'))
      | createCoverSpine ((I.SClo (S, s'), s), Vs, ms) =
	  createCoverSpine ((S, I.comp (s', s)), Vs, ms)

  in
    (* checkOut (G, a @ S) = ()
       checks if the most general goal a @ S' is locally output-covered by a @ S
       Effect: raises Error (msg) otherwise
    *)
    fun checkOut (G, V as I.Root (I.Const (a), S)) =
        let
	  (* already know that subgoal is well-moded *)
	  val SOME(ms) = ModeSyn.modeLookup a
	  val negMs = negateMode ms	(* swap input/output modes *)
	  val V' = createCoverClause (G, V)
	  val V0 = createCoverGoal ((V', I.id), ms) (* replace output by new EVars *)
	  val V0' = abstract (V0, I.id)
	  val missing = cover (V0', negMs, V'::nil, nil)
	  val _ = case missing
	            of nil => ()
		     | _::_ => raise Error ("Output coverage error --- missing cases:\n"
					    ^ missingToString (missing, ms) ^ "\n")
	in
	  ()
	end

    (* checkCovers (a, ms) = ()
       checks coverage for type family a with respect to mode spine ms
       Effect: raises Error (msg) otherwise
    *)
    fun checkCovers (a, ms) =
        let
	  val V0 = initCGoal (a)
	  val _ = CSManager.reset ()
	  val cs = Index.lookup a
	  val ccs = constsToTypes cs	(* calculate covering clauses *)
	  val missing = cover (V0, ms, ccs, nil)
	  val _ = case missing
	            of nil => ()	(* all cases covered *)
		     | _::_ => raise Error ("Coverage error --- missing cases:\n"
					    ^ missingToString (missing, ms) ^ "\n")
	in
	  ()
	end
  end
end;  (* functor Cover *)
