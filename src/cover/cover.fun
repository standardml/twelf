(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure Unify : UNIFY
     sharing Unify.IntSyn = IntSyn'
   structure ModeSyn' : MODESYN
     sharing ModeSyn'.IntSyn = IntSyn'
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure CompSyn : COMPSYN
     sharing CompSyn.IntSyn = IntSyn'
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Paths : PATHS)
  : COVER =
struct
  structure IntSyn = IntSyn'
  structure ModeSyn = ModeSyn'

  exception Error of string

  local
    structure I = IntSyn
    structure M = ModeSyn
    structure C = CompSyn
    structure P = Paths

    (* Coverage goal is represented using all BVars *)

    fun buildSpine 0 = I.Nil
      | buildSpine k = (* k > 0 *)
        I.App (I.Root (I.BVar(k), I.Nil), buildSpine (k-1))

    fun initGoal' (a, k, G, I.Pi ((D, _), V)) =
          initGoal' (a, k+1, I.Decl (G, D), V)
      | initGoal' (a, k, G, I.Uni (I.Type)) =
          (G, I.Root (a, buildSpine k))

    fun initGoal (a) = initGoal' (I.Const (a), 0, I.Null, I.constType (a))

    datatype Equation = Eqn of I.dctx * I.eclo * I.eclo

    datatype Candidates =
        Eqns of Equation list		(* equations to be solved, matches so far *)
      | Cands of int list		(* candidates for splitting, does not match *)
      | Fail				(* more efficient: raise exception *)

    (* Do not raise exception on failure so we may give better error message later *)

    (* fail(cands) = cands'   without adding new candidates *)
    fun fail () = Fail

    (* failAdd (k, cands) = cands'  add new splitting candidate k *)
    fun failAdd (k, Eqns _) = Cands (k::nil) (* no longer matches! *)
      | failAdd (k, Cands (ks)) = Cands (k::ks) (* remove duplicates? *)
      | failAdd (k, Fail) = Fail

    (* addEqn (e, cands) = cands'  add new equation if matches so far *)
    fun addEqn (e, Eqns (es)) = Eqns (e::es) (* still matches *)
      | addEqn (e, cands as Cands (ks)) = (* already failed---ignore new constraints *)
          cands
      | addEqn (e, Fail) = Fail

    fun matchEqns (nil) = true
      | matchEqns (Eqn (G, Us1, Us2)::es) =
        if Unify.unifiable (G, Us1, Us2)
	  then matchEqns (es)
	else false

    fun resolveCands (Eqns (es)) =
        if matchEqns (es) then (Eqns (nil))
	else Fail
      | resolveCands (Cands (ks)) = Cands (ks)

    datatype CandList =
        Covered				(* covered---no candidates *)
      | CandList of (I.Head * Candidates) list (* not covered: list of candidates for each clause *)

    fun addKs (ccs as (c, Cands(ks)), CandList (klist)) = CandList (ccs::klist)
      | addKs (ces as (c, Eqns(nil)), CandList (klist)) = Covered
      | addKs (cfl as (c, Fail), CandList (klist)) = CandList (cfl::klist)

    (* matchAtom (G, d, (P, s'), (Q, s), cands)
       matches coverage goal P[s'] against head Q[s]
       cands = splitting candidates, returns cands'
       Eqns (es) = postponed matching problems.
       Cands (cands) = failure, with candidates `cands'.
       d is depth, k <= d means local variable, k > d means coverage variable.
       Skip over `output' and `ignore' arguments (see matchTopExp, etc)
       Postpone matching and accumlate splitting candidates.
    *)
    fun matchExp (G, d, Us1, Us2, cands) =
        matchExpW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, cands)
    and matchExpW (G, d, Us1 as (I.Root (H1, S1), s1), Us2 as (I.Root (H2, S2), s2), cands) =
        (case (H1, H2)
	   (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (k1), I.BVar(k2)) =>
	      if (k1 = k2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else if k1 > d then failAdd (k1-d, cands) (* H1 is coverage variable *)
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
	    | (I.BVar (k1), I.Const _) =>	(* fail and add H1 as splitting candidate *)
		failAdd (k1-d, cands)
	    | (I.Const _, I.BVar _) => fail ()
            (* no other cases should be possible *)
	    )
     | matchExpW (G, d, (I.Lam (D1, U1), s1), (I.Lam (D2, U2), s2), cands) =
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1, (U1, I.dot1 s1), (U2, I.dot1 s2), cands)
     | matchExpW (G, d, (I.Lam (D1, U1), s1), (U2, s2), cands) =
	   (* eta-expand if necessary *)
	   matchExp (I.Decl (G, I.decSub (D1, s1)), d+1,
		     (U1, I.dot1 s1),
		     (I.Redex (I.EClo (U2, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s2),
		     cands)
     | matchExpW (G, d, (U1, s1), (I.Lam (D2, U2), s2), cands) =
	   matchExp (I.Decl (G, I.decSub (D2, s2)), d+1,
		     (I.Redex (I.EClo (U1, I.shift),
			       I.App (I.Root (I.BVar (1), I.Nil), I.Nil)),
		      I.dot1 s1),
		     (U2, I.dot1 s2),
		     cands)
      | matchExpW (G, d, Us1 as (I.EVar _, s1), Us2, cands) =
	   (* should be irrelevant --- do not add! *)
	   (* should arrange that this is impossible -fp *)
	   cands
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
		       M.Mapp (_, ms'), cands) = (* Skip Output or Ignore argument *)
	   matchTopSpine (G, (S1, s1), (S2, s2), ms', cands)

    fun matchClause (G, ps', (C.Eq Q, s), ms) =
          resolveCands (matchTop (G, ps', (Q, s), ms))
      | matchClause (G, ps', (C.And (r, A, g), s), ms) =
	let
	  val X = I.newEVar (G, I.EClo(A, s)) (* redundant? *)
	in
	  matchClause (G, ps', (r, I.Dot(I.Exp(X), s)), ms)
	end
      | matchClause (G, ps', (C.Exists (I.Dec (_, A), r), s), ms) =
	let
	  val X = I.newEVar (G, I.EClo(A, s))
	in
	  matchClause (G, ps', (r, I.Dot (I.Exp (X), s)), ms)
	end
      (* C.Assign, C.In, and C.Exists' not supported *)

    (* invariant klist <> Covered *)
    fun matchSig (G, ps', nil, ms, klist) = klist
      | matchSig (G, ps', I.Const(c)::sgn', ms, klist) =
        let
	  val C.SClause(r) = C.sProgLookup c
	  val cands = CSManager.trail
	              (fn () => matchClause (G, ps', (r, I.id), ms))
	in
	  matchSig' (G, ps', sgn', ms, addKs ((I.Const(c),cands), klist))
	end
      | matchSig (G, ps', _::sgn', ms, klist) = matchSig (G, ps', sgn', ms, klist)

    and matchSig' (G, ps', sgn, ms, Covered) = Covered (* already covered: return *)
      | matchSig' (G, ps', sgn, ms, CandList (klist)) = (* not yet covered: continue to search *)
          matchSig (G, ps', sgn, ms, CandList (klist))

    (* match *)
    (* no local assumptions *)
    fun match (G, V as I.Root (I.Const (a), S), ms) =
        matchSig (G, (V, I.id), Index.lookup a, ms, CandList (nil))

    (*** Selecting Splitting Variable ***)

    fun selectCand (Covered) = Covered	(* success: case is covered! *)
      | selectCand (CandList (klist)) = selectCand' klist
    and selectCand' nil = CandList (nil) (* failure: case G,V is not covered! *)
      | selectCand' ((c, Fail)::klist) = (* local failure (clash) and no candidates *)
          selectCand' klist
      | selectCand' ((c, Cands(nil))::klist) = (* local failure (dependency) but no candidates *)
	  selectCand' klist
      | selectCand' ((c, Cands(k::ks))::klist) = (* found candidate: pick first one *)
	  CandList ((c, Cands(k::nil))::nil)

    (*** Splitting ***)

    fun buildPi (I.Null, V, n) = (V, n)
      | buildPi (I.Decl (G, D), V, n) =
          buildPi (G, I.Pi ((D, I.Maybe), V), n+1)

    fun instEVars (Vs, n, Xopt) = instEVarsW (Whnf.whnf Vs, n, Xopt)
    and instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), n, Xopt) =
        let
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
	in
	  instEVars ((V2, I.Dot (I.Exp (X1), s)), n-1,
		     if n = 0 then SOME(X1) else Xopt)
	end
      | instEVarsW (Vs as (I.Root _, s), n, Xopt) = (Vs, Xopt)

    local 
      val caseList : (I.dctx * I.Exp) list ref = ref nil
    in
      fun resetCases () = (caseList := nil)
      fun addCase (G, V) = (caseList := (G, V) :: !caseList)
      fun getCases () = (!caseList)
    end

    (* splitEVar X sc = ()  --- call sc on all possibilities for X *)
    fun splitEVar X sc = ()

    (* abstract (V, s) = (G, V') *)
    fun abstract (V, s) = (I.Null, I.EClo (V, s))

    fun splitVar (G, V, k) =
        let
	  val (V1, n) = buildPi (G, V, 0) (* V1 has explicit Pi's for G *)
	  val ((V2, s), SOME(X)) = instEVars ((V1, I.id), n-k, NONE)
					(* split on n-k'th variable, starting at 0 *)
	  val _ = resetCases ()
	  val _ = splitEVar X (fn () => addCase (abstract (V2, s)))
	in
	  getCases ()
	end

    fun cover (G, V, ms, missing) = split (G, V, selectCand (match (G, V, ms)), ms, missing)
    and split (G, V, Covered, ms, missing) = missing
      | split (G, V, CandList (nil), ms, missing) = ((G, V)::missing)
      | split (G, V, CandList ((_, Cands (k::_))::_), ms, missing) =
          covers (splitVar (G, V, k), ms, missing)
    and covers (nil, ms, missing) = missing
      | covers ((G0, V0)::cases', ms, missing) =
          covers (cases', ms, cover (G0, V0, ms, missing))

  in
    fun checkCovers (a, ms) =
        let
	  val _ = print "Coverage checking not yet implemented!\n"
	  val (G0, V0) = initGoal (a)
	  (* val (G0, (V, s)) = CFormToCGoal (I.Null, (F0, I.id)) *)
	  val missing = cover (G0, V0, ms, nil)
	  val _ = case missing
	            of nil => print "Coverage satisfied!\n"
		     | _ => print ("Coverage: " ^ Int.toString (List.length missing)
				   ^ " case(s) missing!\n")
	in
	  ()
	end
  end
end;  (* functor Cover *)
