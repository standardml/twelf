(* Coverage Checking *)
(* Author: Frank Pfenning *)

functor Cover
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Whnf : WHNF
     sharing Whnf.IntSyn = IntSyn'
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

    datatype CForm =
      InCover of I.Dec * CForm
    | OutCover of I.Dec * CForm
    | Ignore of I.Dec * CForm
    | Atom of I.Exp			(* always I.Root (a, S) *)

    fun buildSpine 0 = I.Nil
      | buildSpine k = (* k > 0 *)
        I.App (I.Root (I.BVar(k), I.Nil), buildSpine (k-1))

    fun modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Plus,_), ms)) =
        InCover (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Minus,_), ms)) =
	OutCover (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Pi ((D,_), V), M.Mapp (M.Marg(M.Star,_), ms)) =
	Ignore (D, modeToCForm' (a, k+1, V, ms))
      | modeToCForm' (a, k, I.Uni (I.Type), M.Mnil) =
	Atom (I.Root (a, buildSpine k))

    fun modeToCForm (a, ms) =
        modeToCForm' (I.Const a, 0, I.constType a, ms)

    (* CFormToGoal (G, (F, s)) = (G', (V, s')) *)
    fun CFormToCGoal (G, (InCover (D, F), s)) =
           CFormToCGoal (I.Decl (G, D), (F, I.dot1 s))
      | CFormToCGoal (G, (OutCover (I.Dec (_, V), F), s)) =
	let
	  val X = I.newEVar (G, I.EClo (V, s))
	  (* val X' = Whnf.lowerEVar X *)
	in
	  CFormToCGoal (G, (F, I.Dot (I.Exp X, s)))
	end
      | CFormToCGoal (G, (Ignore (I.Dec (_, V), F), s)) =
	let
	  val X = I.newEVar (G, I.EClo (V, s))
	in
	  CFormToCGoal (G, (F, I.Dot (I.Exp X, s)))
	end
      | CFormToCGoal (G, (Atom (V), s)) = (G, (V, s))

    datatype Equation = Eqn of I.dctx * I.eclo * I.eclo

    datatype Candidates =
        Eqns of Equation list		(* equations to be solved, matches so far *)
      | Cands of int list		(* candidates for splitting, does not match *)

    (* fail(cands) = cands'   without adding new candidates *)
    fun fail (Eqns _) = Cands (nil)
      | fail (cands) = cands

    (* failAdd (k, cands) = cands'  add new splitting candidate k *)
    fun failAdd (k, Eqns _) = Cands (k::nil) (* no longer matches! *)
      | failAdd (k, Cands (ks)) = Cands (k::ks) (* remove duplicates? *)

    (* addEqn (e, cands) = cands'  add new equation if matches so far *)
    fun addEqn (e, Eqns (es)) = Eqns (e::es) (* still matches *)
      | addEqn (e, cands as Cands (ks)) = (* already failed---ignore new constraints *)
          cands

    fun matchEqns (nil) = true
      | matchEqns (Eqn (G, Us1, Us2)::es) =
        if Unify.unifiable (G, Us1, Us2)
	  then matchEqns (es)
	else false

    fun resolveCands (Eqns (es)) =
        if matchEqns (es) then (Eqns (nil))
	else Cands (nil)
      | resolveCands (Cands (ks)) = Cands (ks)

    datatype CandList =
        Covered				(* covered---no candidates *)
      | CandList of (I.Head * Candidates) list (* not covered: list of candidates for each clause *)

    fun addKs (ccs as (c, Cands(ks)), CandList (klist)) = CandList (ccs::klist)
      | addKs (ces as (c, Eqns(nil)), CandList (klist)) = Covered

    (* matchAtom (G, d, (P, s'), (Q, s), cands)
       matches coverage goal P[s'] against head Q[s]
       cands = splitting candidates, returns cands'
       Eqns (es) = postponed matching problems.
       Cands (cands) = failure, with candidates `cands'.
       d is depth, k <= d means local variable, k > d means coverage variable.
       Skip over `output' and `ignore' arguments.
       !!NOT YET IMPLEMENTED!!
       !! Currently incomplete because of that !!
       Postpone unification and accumlate splitting candidates.
    *)
    fun matchExp (G, d, Us1, Us2, cands) =
        matchExpW (G, d, Whnf.whnf Us1, Whnf.whnf Us2, cands)
    and matchExpW (G, d, Us1 as (I.Root (H1, S1), s1), Us2 as (I.Root (H2, S2), s2), cands) =
        (case (H1, H2)
	    (* No skolem constants, foreign constants, FVars *)
	   of (I.BVar (k1), I.BVar(k2)) =>
	      if (k1 = k2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else if k1 > d then failAdd (k1-d, cands) (* H1 is coverage variable *)
		   else fail(cands) (* otherwise fail with no new candidates *)
	    | (I.Const(c1), I.Const(c2)) =>
	      if (c1 = c2) then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else fail(cands) (* fail with no new candidates *)
            | (I.Def (d1), I.Def (d2)) =>
	      if (d1 = d2)		(* strictness enforced *)
		then matchSpine (G, d, (S1, s1), (S2, s2), cands)
	      else matchExpW (G, d, Whnf.expandDef Us1, Whnf.expandDef Us2, cands)
	    | (I.Def (d1), _) => matchExpW (G, d, Whnf.expandDef Us1, Us2, cands)
	    | (_, I.Def (d2)) => matchExpW (G, d, Us1, Whnf.expandDef Us2, cands)
	    | (I.BVar (k1), _) => (* H2 is Const, not BVar or Def *)
		failAdd (k1-d, cands)	(* fail and add H1 as splitting candidate *)
	    | _ => (* other head mismatch, now new candidates *)
		fail(cands))
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

    fun matchClause (G, ps', (C.Eq Q, s)) =
          resolveCands (matchExp (G, 0, ps', (Q, s), Eqns (nil)))
      | matchClause (G, ps', (C.And (r, A, g), s)) =
	let
	  val X = I.newEVar (G, I.EClo(A, s)) (* redundant? *)
	in
	  matchClause (G, ps', (r, I.Dot(I.Exp(X), s)))
	end
      | matchClause (G, ps', (C.Exists (I.Dec (_, A), r), s)) =
	let
	  val X = I.newEVar (G, I.EClo(A, s))
	in
	  matchClause (G, ps', (r, I.Dot (I.Exp (X), s)))
	end
      (* C.Assign, C.In, and C.Exists' not supported *)

    (* invariant klist <> Covered *)
    fun matchSig (G, ps', nil, klist) = klist
      | matchSig (G, ps', I.Const(c)::sgn', klist) =
        let
	  val _ = if !Global.chatter > 4
		    then print (Names.constName (c) ^ " ")
		  else ()
	  val C.SClause(r) = C.sProgLookup c
	  val cands = CSManager.trail
	              (fn () => matchClause (G, ps', (r, I.id)))
	in
	  matchSig' (G, ps', sgn', addKs ((I.Const(c),cands), klist))
	end
      | matchSig (G, ps', _::sgn', klist) = matchSig (G, ps', sgn', klist)

    and matchSig' (G, ps', sgn, Covered) = Covered (* already covered: return *)
      | matchSig' (G, ps', sgn, CandList (klist)) = (* not yet covered: continue to search *)
          matchSig (G, ps', sgn, CandList (klist))

    (* match *)
    (* no local assumptions *)
    fun match (G, ps' as (I.Root (I.Const (a), S), s)) =
        matchSig (G, ps', Index.lookup a, CandList (nil))

  in
    fun checkCovers (a, ms) =
        let
	  val _ = print "Coverage checking not yet implemented!\n"
	  val F0 = modeToCForm (a, ms)
	  val (G0, (V, s)) = CFormToCGoal (I.Null, (F0, I.id))
	  val _ = if !Global.chatter > 4
		    then print "Coverage [ "
		  else ()
	  val klist = match (G0, (V, s))
	  val _ = if !Global.chatter > 4
		    then print "]\n"
		  else ()
	  val _ = case klist
	            of Covered => print "Coverage satisfied!\n"
		     | CandList (hks) => print "Coverage failed!\n"
	in
	  ()
	end
  end
end;  (* functor Cover *)
