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
   structure ModeSyn' : MODESYN
     sharing ModeSyn'.IntSyn = IntSyn'
   structure Index : INDEX
     sharing Index.IntSyn = IntSyn'
   structure CompSyn : COMPSYN
     sharing CompSyn.IntSyn = IntSyn'
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
    structure C = CompSyn
    structure P = Paths
    structure F = Print.Formatter

    (* Coverage goal is represented using all BVars *)

    fun buildSpine 0 = I.Nil
      | buildSpine k = (* k > 0 *)
        I.App (I.Root (I.BVar(k), I.Nil), buildSpine (k-1))

    fun initGoal' (a, k, G, I.Pi ((D, P), V)) =
        let
	  val D' = Names.decEName (G, D)
	in
          I.Pi ((D', I.Maybe), initGoal' (a, k+1, I.Decl (G, D'), V))
	end
      | initGoal' (a, k, G, I.Uni (I.Type)) =
          I.Root (a, buildSpine k)

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
      | resolveCands (Fail) = Fail

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
		       M.Mapp (M.Marg (M.Star, _), ms'), cands) =
	(* skip "ignore" arguments, later also "output" arguments *)
	   matchTopSpine (G, (S1, s1), (S2, s2), ms', cands)
      | matchTopSpine (G, (I.App (U1, S1), s1), (I.App (U2, S2), s2),
		       M.Mapp (M.Marg (M.Minus, _), ms'), cands) =
	raise Error ("Output coverage not yet implemented")

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
      | match (G, I.Pi ((D, _), V'), ms) =
	match (I.Decl (G, D), V', ms)

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

    (*
    fun buildPi (I.Null, V, n) = (V, n)
      | buildPi (I.Decl (G, D), V, n) =
          buildPi (G, I.Pi ((D, I.Maybe), V), n+1)
    *)

    fun instEVars (Vs, XsRev) = instEVarsW (Whnf.whnf Vs, XsRev)
    and instEVarsW ((I.Pi ((I.Dec (xOpt, V1), _), V2), s), XsRev) =
        let
	  val X1 = I.newEVar (I.Null, I.EClo (V1, s)) (* all EVars are global *)
	in
	  instEVars ((V2, I.Dot (I.Exp (X1), s)), X1::XsRev)
	end
      | instEVarsW (Vs as (I.Root _, s), XsRev) = (Vs, XsRev)

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
       then . |- U' = c @ (Xn; .. Xn; Nil)
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


    (* splitEVar X sc = ()  --- call sc on all possibilities for X *)

    fun splitEVar ((X as I.EVar (_, GX, V, _)), sc) = (* GX = I.Null *)
          lowerSplit (I.Null, (V, I.id),
		      fn U => if Unify.unifiable (I.Null, (X, I.id), (U, I.id)) (* always succeeds? *)
				then sc ()
			      else ())

    (* abstract (V, s) = (G, V') *)
    fun abstract (V, s) = 
        let
	  val (i, V') = Abstract.abstractDecImp (I.EClo (V, s))
	in
	  V'
	end

    fun splitVar (V, k) =
        let
	  val ((V1, s), XsRev) = instEVars ((V, I.id), nil)
          (* split on k'th variable, counting from innermost *)
	  val X = List.nth (XsRev, k-1)
	  val _ = resetCases ()
	  val _ = splitEVar (X, fn () => addCase (abstract (V1, s)))
	in
	  getCases ()
	end

    (* fix formatGoal to pick existential and universal names appropriately according to mode *)
    fun formatGoal (V) = Print.formatExp (I.Null, V)
    fun formatGoals (V::nil) = [formatGoal (V)]
      | formatGoals (V::Vs) =
          Print.formatExp (I.Null, V) :: F.String "," :: F.Break :: formatGoals Vs

    fun missingToString (Vs) =
        F.makestring_fmt (F.Hbox [F.Vbox0 0 1 (formatGoals Vs), F.String "."])

    fun cover (V, ms, missing) =
        let 
	  val _ = if !Global.chatter >= 5
		    then print ("Goal : " ^ F.makestring_fmt (formatGoal V) ^ "\n")
		  else ()
	in
	  split (V, selectCand (match (I.Null, V, ms)), ms, missing)
	end
    and split (V, Covered, ms, missing) = missing
      | split (V, CandList (nil), ms, missing) = (V::missing)
      | split (V, CandList ((_, Cands (k::_))::_), ms, missing) =
          covers (splitVar (V, k), ms, missing)
    and covers (nil, ms, missing) = missing
      | covers (V::cases', ms, missing) =
          covers (cases', ms, cover (V, ms, missing))

  in
    fun checkCovers (a, ms) =
        let
	  (* val _ = print "Coverage checking not yet implemented!\n" *)
	  val V0 = initGoal (a)
	  (* val (G0, (V, s)) = CFormToCGoal (I.Null, (F0, I.id)) *)
	  val _ = CSManager.reset ()
	  val missing = cover (V0, ms, nil)
	  val _ = case missing
	            of nil => print "Coverage satisfied!\n"
		     | _ => print ("Coverage failed!  Missing cases:\n"
				   ^ missingToString missing ^ "\n")
	in
	  ()
	end
  end
end;  (* functor Cover *)
