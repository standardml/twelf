structure Reductio =
struct
	exception Unimp
	exception Error of string
	exception Matching of string
	exception NonPattern
	exception NotFound of string

        open Syntax

	datatype kinding_constraint = 
		 CON_LF (* Pi- only *)
	       | CON_PLUS (* Pi-, Pi+, [Pi] matched by strict occ in later args
                             not necessarily in return type *)
	       | CON_MINUS (* All Pis, and [Pi] can use strict occs in later args
                              and in return type. *)

        (* left side is open, (with respect to outer pi bindings)
           and right side is closed *)
	datatype eq_c = EltC of spinelt * spinelt
		      | SpineC of spine * spine
		      | TypeC of tp * tp
	type tp_c = term * tp

        (* equality checking *)
	fun tp_eq (TRoot (n, sp), TRoot(n', sp')) = type_const_head_eq(n, n', sp, sp')
	  | tp_eq (TPi(m,a,b),TPi(m',a',b')) = m = m' andalso tp_eq (a,a') andalso tp_eq (b,b')
	  | tp_eq _ = false
	and sp_eq ([],[]) = true
	  | sp_eq (e::sp, e'::sp') = elt_eq (e,e') andalso sp_eq (sp, sp')
	  | sp_eq _ = false
	and elt_eq (t, t') = elt_eq' (elt_eroot_elim t, elt_eroot_elim t')
	and elt_eq' (Elt t, Elt t') = tm_eq (t, t')
	  | elt_eq' (AElt t, AElt t') = atm_eq (t, t')
	  | elt_eq' (Ascribe (t, a), Ascribe (t', a')) = ntm_eq (t,t') andalso tp_eq (a,a')
	  | elt_eq' (Omit, Omit) = true
	  | elt_eq' _ = false
	and tm_eq (NTerm t, NTerm t') = ntm_eq (t, t')
	  | tm_eq (ATerm t, ATerm t') = atm_eq (t, t')
	  | tm_eq _ = false
	and atm_eq (tm as ARoot(Const n,sp), tm' as ARoot(Const n',sp')) = const_head_eq(n, n', sp, sp', ATerm tm, ATerm tm')
	  | atm_eq (ARoot(Var n,sp),ARoot(Var n',sp')) = n = n' andalso sp_eq (sp, sp')
	  | atm_eq _ = false (* ERoots are taken care of at the spine element level *)
	and ntm_eq (t, t') = ntm_eq' (ntm_eroot_elim t, ntm_eroot_elim t')
	and ntm_eq' (tm as NRoot(Const n,sp), tm' as NRoot(Const n',sp')) = const_head_eq(n, n', sp, sp', NTerm tm, NTerm tm')
	  | ntm_eq' (Lam t, Lam t') = tm_eq (t, t')
	  | ntm_eq' _ = false
        (* determine whether two roots are equal. n and n' are the cids of the heads, whether the
           roots happen to be nroots or aroots. sp and sp' are the spines, and tm and tm' are the
           entire roots. *)
	and const_head_eq (n, n', sp, sp', tm, tm') =
 	    let
		val def = Sgn.def n
		val def' = Sgn.def n'
		val eq_and_strict = (n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n)))
 		fun redux t n sp = reduce(srTerm(t, typeOf(Sgn.classifier n)), sp) 
	    in
		    case (eq_and_strict, def, def') of 
			(true, _, _) => sp_eq(sp, sp')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => false
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_TERM t') => tm_eq(redux t n sp, redux t' n' sp')
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_NONE) => tm_eq(redux t n sp, tm')
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TERM t') => tm_eq(tm, redux t' n' sp')
		      | _ => raise Syntax "invariant violation"
	    end
         (* similar thing for atomic types. Here we need not include redundant arguments for the entire
            TRoot since there is only one kind of TRoot (not both ARoot and NRoot in the case of terms)
            so we just build it back up from scratch *)
	and type_const_head_eq (n, n', sp, sp') =
 	    let
		val def = Sgn.def n
		val def' = Sgn.def n'
		val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n))
		fun redux a n sp = tp_reduce(a, kindOf(Sgn.classifier n), sp)
	    in
		    case (eq_and_strict, def, def') of 
			(true, _, _) => sp_eq(sp, sp')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => false
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_TYPE a') => tp_eq(redux a n sp, redux a' n' sp')
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_NONE) => tp_eq(redux a n sp, TRoot(n',sp'))
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TYPE a') => tp_eq(TRoot(n,sp), redux a' n' sp')
		      | _ => raise Syntax "invariant violation"
	    end

        (* is an equality constraint satisfied? *)
	fun eq_c_true (EltC(e,e')) = elt_eq(e, e')
	  | eq_c_true (SpineC(s,s')) = sp_eq(s, s')
	  | eq_c_true (TypeC(a,a')) = tp_eq(a, a')

        (* The type ppsubst is a compact way of representing a
           class of substitutions that contains all of the pattern
           substitutions. These are the "prepattern" substitutions,
           the ones that are of the form 
           i1.i2. ... in . shift^m
           where all the i1...in are variables. *)
        (* ([i1, i2, ... , in], m) represents i1.i2. ... in . shift^m *)
	type ppsubst = int list * int

	(* pp_shift pps m: compute pps o shift^m *)
	fun pp_shift (vs,shift) m = 
	    let 
		val len = length vs
	    in
		if m < len
		then (List.drop(vs, m),shift)
		else ([], m - len + shift)
	    end

        (* pp_nth: extract the result of applying a ppsubst to the nth variable *)
	fun pp_nth (vs,shift) n = 
	    let 
		val len = length vs
	    in
		if n < len 
		then List.nth(vs, n) 
		else n - len + shift
	    end

        (* pp_o: compose two ppsubsts *)
	fun pp_o (pps, (vs, shift)) = 
	    let
		val (vs', shift') =  pp_shift pps shift
	    in
		((map (pp_nth pps) vs) @ vs', shift')
	    end

        (* pp_comp: compose a list of ppsubsts *)
	fun pp_comp ppsl = foldr pp_o ([],0) ppsl

        (* pp_normalize s
           if a substitution s is equal to a 'prepattern'
           i1.i2. ... in . shift^m (no restriction on the i's being distinct)
           returns ([i1, i2, ... , in], m).
           Otherwise raises Domain. *)
	fun pp_normalize s = pp_normalize' s
	and pp_normalize' Id = ([], 0)
	  | pp_normalize' (TermDot(t, a, s)) =
	    let 
                 (* if the term being consed on is not an eta-expansion of
                    a variable, forget about it *)
		 val v = Strict.eta_contract_var (Elt t) handle Strict.EtaContract => raise Domain
		 val (vs, shift) = pp_normalize' s
	     in
		 (v::vs, shift)
	     end
	  | pp_normalize' (ZeroDotShift s) = 
	    let 
		val (vs, shift) = pp_normalize' s
	    in
		(0 :: (map (fn x => x + 1) vs), shift + 1)
	    end
	  | pp_normalize' (Shift (n, m)) = 
	    (* using the fact that Shift (n+1) m = ZeroDotShift (Shift n m) *)
	    (List.tabulate (n, (fn x => x)), n + m)
	  | pp_normalize' (EVarDot _) = raise Domain (* XXX: Correct??? *)
	  | pp_normalize' (VarOptDot (no, s)) = 
	    let 
		val (vs, shift) = pp_normalize' s
	    in
		case no of 
		    SOME n => (n :: vs, shift)
		  | NONE => raise Error "??? I'm not sure this is really wrong"
	    end
	  | pp_normalize' (Compose sl) = prepattern (substs_comp sl)

	(* prepattern: convert a subst into a ppsubst *)
        (* raises Domain if it is not a prepattern *)
	and prepattern (s : subst) = pp_normalize s

	(* pp_ispat: is this ppsubst a pattern substitution? *)
	fun pp_ispat ([],shift) = true
	  | pp_ispat (n::s,shift) = let fun isn x = (x = n)
				     fun hasn s = List.exists isn s
				 in
				     n < shift andalso
				     not (hasn s) andalso
				     pp_ispat (s,shift)
				 end

        (* take a list of int options and a shift value and
        produce an actual substitution. This is morally a one-sided
        inverse to pp_normalize *)
	fun makesubst ([],0) = Id
	  | makesubst ([],shift) = Shift (0, shift)
	  | makesubst (v::vs,shift) = VarOptDot (v, makesubst (vs,shift))

        (* take in a ppsubst and return a substitution (which may involve VarOptDots) that is its inverse. *)
	fun pp_invert (vs,shift) =
	    let
		val inds = List.tabulate(shift, (fn x => x))
		fun search n [] (x : int) = NONE
		  | search n (h::tl) x = 
		    if x = h 
		    then SOME n
		    else search (n+1) tl x
	    in
		makesubst (map (search 0 vs) inds, length vs)
	    end 

        (* Here begins all the matching code.
           flex_left takes an uninstantiated evar, a substitution, and a right-hand-side of an equation.
           The equation is
           E[sl] = RHS
           If it can successfully instantiate E with RHS[sl^-1], then it does so
           imperatively and returns ().

           If sl is not pattern it raises NonPattern.
           If RHS is not in the range of sl, then MissingVar is raised by substitution *)
	fun flex_left ((r as ref NONE,a), s : subst, rhs) = 
	    let
		val pps = prepattern s handle Domain => raise NonPattern
		val _ = if pp_ispat pps then () else raise NonPattern
		val ppsi = pp_invert pps
		val rhs' = subst_term ppsi (termof rhs)
		val _ = r := SOME rhs'
	    in
		()
	    end
	  | flex_left _ = raise Error "evar invariant violated"

        (* match_one' takes an equation (which by invariant does not
           have an instantiated evar on the left, and is ground on the
           right) and returns a list of smaller equations that are
           equivalent to it, or else throws NonPattern in the event
           that it finds a flex-rigid equation where the flex side is
           not pattern. *)

	(* XXX this just_one stuff is here for debugging: replace with match_one *)
	fun just_one c = [c]
	and just_one' c = [c]
	and match_one' (EltC(Elt(NTerm(Lam t)),Elt(NTerm(Lam t')))) =
	    just_one (EltC(Elt t, Elt t'))
	  | match_one' (EltC(elt as Elt(NTerm(NRoot(Const n,s))), elt' as Elt(NTerm(NRoot(Const n',s'))))) =
	    match_const_head(n,n',s,s',elt,elt',"c- head mismatch")
	  | match_one' (EltC(elt as Elt(ATerm(ARoot(Const n,s))), elt' as Elt(ATerm(ARoot(Const n',s'))))) =
	    match_const_head(n,n',s,s',elt,elt',"c+ head mismatch")
	  | match_one' (EltC(Elt(ATerm(ARoot(Var n,s))),Elt(ATerm(ARoot(Var n',s'))))) =
	    if n = n' 
	    then just_one' (SpineC(s, s'))
	    else raise Matching "var head mismatch"
	  | match_one' (EltC(AElt t,AElt t')) =
	    just_one' (EltC(Elt(ATerm t), Elt(ATerm t')))
	  | match_one' (EltC(Ascribe(m,a),Ascribe(m',a'))) =
	    match_two (EltC(Elt(NTerm m), Elt(NTerm m'))) (TypeC(a, a'))
	  | match_one' (EltC(Omit,Omit)) = []
	  | match_one' (TypeC(TPi(m,a,b),TPi(m',a',b'))) = 
	    if m = MINUS andalso m' = MINUS
	    then match_two (TypeC(a, a')) (TypeC(b, b'))
	    else raise Matching "mode mismatch"
	  | match_one' (TypeC(TRoot(n,s), TRoot(n',s'))) = match_type_const_head (n, n', s, s', "type family mismatch")
	  | match_one' (SpineC([],[])) = []
	  | match_one' (SpineC(h::s,h'::s')) = match_two (EltC(h, h'))  (SpineC(s, s'))
	  | match_one' (EltC(Elt(ATerm(ERoot(ev,s : subst))), elt)) = (flex_left (ev, s, elt); [])
	  | match_one' x = raise Matching "doesn't match"

	(* PERF: this second elt_eroot_elim on elt' seems like it ought to be unnecessary if
	     I eliminate all eroots at synth time *)
	and match_one (EltC(elt,elt')) = match_one' (EltC(elt_eroot_elim elt, elt_eroot_elim elt')) 
	  | match_one e = match_one' e
	and match_two e1 e2 = [e1, e2] 
	and match_const_head (n, n', s, s', elt, elt', err) =
 	    let
		val def = Sgn.def n
		val def' = Sgn.def n'
		val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n))
		fun redux t n sp = reduce(srTerm(t, typeOf(Sgn.classifier n)), sp)
		val eq = 	
		    case (eq_and_strict, def, def') of 
			(true, _, _) => SpineC(s, s')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => raise Matching err
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_TERM t') => EltC(Elt(redux t n s), Elt(redux t' n' s'))
		      | (_, Sgn.DEF_TERM t, Sgn.DEF_NONE) => EltC(Elt(redux t n s), elt')
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TERM t') => EltC(elt, Elt(redux t' n' s'))
		      | _ => raise Matching "invariant violation"
	    in
		just_one' eq
	    end 
	and match_type_const_head (n, n', s, s', err) =
 	    let
		val def = Sgn.def n
		val def' = Sgn.def n'
		val eq_and_strict = n = n' andalso (def = Sgn.DEF_NONE orelse not (Sgn.abbreviation n))
		fun redux a n sp = tp_reduce(a, kindOf(Sgn.classifier n), sp)
		val eq = 	
		    case (eq_and_strict, def, def') of 
			(true, _, _) => SpineC(s, s')
		      | (false, Sgn.DEF_NONE, Sgn.DEF_NONE) => raise Matching err
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_TYPE a') => TypeC(redux a n s, redux a' n' s')
		      | (_, Sgn.DEF_TYPE a, Sgn.DEF_NONE) => TypeC(redux a n s, TRoot(n', s'))
		      | (_, Sgn.DEF_NONE, Sgn.DEF_TYPE a') => TypeC(TRoot(n, s), redux a' n' s')
		      | _ => raise Matching "invariant violation"
	    in
		just_one' eq
	    end

	fun matching (p) =  let
	    fun matching' (c::p,p') =
		(let val eqs = match_one c in matching'(eqs @ p, p') end
		 handle NonPattern => matching'(p, c::p'))
	      | matching' ([], p') = p'
	in
	    matching' (p,[]) 
	end


(*	fun ctxcons (a, G) = map (shift_tp 0) (a::G) *)
	fun ctxcons (a, G) = a::G

	datatype cg_mode = CG_SYNTH
			 | CG_CHECK of tp

(* 	val constraint_gen : tp list -> spine * tp * cg_mode -> eq_c list * tp_c list
        fun constraint_gen G (s, z, c) = (p, q, aopt) *)
	(* invariants: 
	   s is ground
	   if c is CG_CHECK c', then c' is ground 
           right-hand sides of p,q are ground
           left-hand sides of p,q and z may involve evars
           
           the returned aopt...
           ... is SOME of a type if c was CG_SYNTH
           ... is NONE           if c was CG_CHECK of something *)

	fun constraint_gen G (s, z, c) = constraint_gen' G (s, z, c)
	and constraint_gen' G ([], a as TRoot _, CG_CHECK(a' as TRoot _)) = 
	    ([TypeC(a,a')], [], NONE) (* PERF: we might be able to reject this faster if we knew a and a'
                                         were not defined types and were different *)
	  | constraint_gen' G ([], TRoot(n,s), CG_SYNTH) = 
	     ([], [], SOME(TRoot(n, s)))
	  | constraint_gen' G (Omit::s, TPi(OMIT, a, z), c) =
	    let 
		val ev : evar = (ref NONE, a)
		val z' = subst_tp (EVarDotId ev) z
		val (p,q,aa) = constraint_gen' G (s, z', c)
	    in
		(p, q, aa)
	    end
	  | constraint_gen' G ((Elt m)::s, TPi(MINUS, a, z), c) =
	    let 
		val z' = subst_tp (TermDot (m, a, Id)) z
		val (p,q,aa) = constraint_gen' G (s, z', c)
	    in
		(p, (m,a)::q, aa)
	    end
	  | constraint_gen' G ((AElt m)::s, TPi(PLUS, a, z), c) =
	    let 
		val a' = synth(G, m)
		val z' = subst_tp (TermDot (ATerm m, a, Id)) z
		val (p,q,aa) = constraint_gen' G (s, z', c)
	    in
                (* Same PERF comment here as above *)
		((TypeC(a,a'))::p, q, aa)
	    end
	  | constraint_gen' G ((Ascribe(m,a'))::s, TPi(PLUS, a, z), c) =
	    let 
		val z' = subst_tp (TermDot (NTerm m, a, Id)) z
		val (p,q,aa) = constraint_gen' G (s, z', c)
	    in
                (* As well as here *)
		((TypeC(a,a'))::p, q, aa)
	    end
	  | constraint_gen' _ _ = raise Error "spine doesn't match type"

        (* similar to above but we just have a putative type and its kind, and return nothing but constraints *)
	and tp_constraint_gen G ([], Type) =  ([], [])
	  | tp_constraint_gen G (Omit::s, KPi(OMIT, a, z)) =
	    let 
		val ev : evar = (ref NONE, a)
		val z' = subst_knd (EVarDotId ev) z
		val (p,q) = tp_constraint_gen G (s, z')
	    in
		(p, q)
	    end
	  | tp_constraint_gen G ((Elt m)::s, KPi(MINUS, a, z)) =
	    let 
		val z' = subst_knd (TermDot (m, a, Id)) z
		val (p,q) = tp_constraint_gen G (s, z')
	    in
		(p, (m,a)::q)
	    end
	  | tp_constraint_gen G ((AElt m)::s, KPi(PLUS, a, z)) =
	    let 
		val a' = synth(G, m)
		val z' = subst_knd (TermDot (ATerm m, a, Id)) z
		val (p,q) = tp_constraint_gen G (s, z')
	    in
		((TypeC(a,a'))::p, q)
	    end
	  | tp_constraint_gen G ((Ascribe(m,a'))::s, KPi(PLUS, a, z)) =
	    let 
		val z' = subst_knd (TermDot (NTerm m, a, Id)) z
		val (p,q) = tp_constraint_gen G (s, z')
	    in
		((TypeC(a,a'))::p, q)
	    end
	  | tp_constraint_gen _ _ = raise Error "spine doesn't match type"

	and check_equality_constraints p = List.all eq_c_true p

	and check_typing_constraints G q = List.all (fn (m,a) => check(G, m, a)) q

        (* returns true on success or raises Matching on failure *)
	and matching_succeeds G (p,q) =
	    let
 		val p' = matching p (* evar side-effects affect q, raises Matching if matching fails *)
		val _ = if check_equality_constraints p' then () else raise Matching "residual equality constraints failed"
		val _ = if check_typing_constraints G q then () else raise Matching "residual typing constraints failed"
	    in
		true
	    end

	and check_spinelt (G, Elt t, a) = check(G, t, a)
	  | check_spinelt (G, AElt t, a) = check(G, ATerm t, a)
	  | check_spinelt (G, Ascribe(t,a), a') = (tp_eq(a, a') andalso check(G, NTerm t, a))
	  | check_spinelt (G, Omit, _) = raise Error "cannot check omitted arguments"

	and check (G, NTerm(Lam(t)), TPi(_,a,b)) = check(ctxcons (a, G), t, b)
	  | check (G, ATerm(t), a) = (tp_eq(synth(G, t), a) handle Error s =>  false)
	  | check (G, NTerm(NRoot(Const n, s)), a) = 
	    let
		 val b = case Sgn.classifier n of 
			     tclass b => b
			   | _ => raise Error "signature invariant violated!"
		 val (p, q, _) = constraint_gen G  (s, b, CG_CHECK a) (* creates ref cells for evars *)
	     in
		 matching_succeeds G (p, q)
	     end
	  | check _ = false
	and check_kind (G, Type) = true
	  | check_kind (G, KPi(OMIT,a,k)) = check_type CON_LF (G,a) andalso 
					    check_kind(ctxcons (a, G), k) andalso
					    Strict.check_strict_kind(k)
	  | check_kind (G, KPi(_,a,k)) = check_type CON_LF (G,a) andalso
					 check_kind(ctxcons (a, G), k)

	and check_type _ (G, TRoot(n, s)) = 
	    let
		val k = case Sgn.classifier n of 
			    kclass k => k
			  | _ => raise Error "signature invariant violated!"
		val (p, q) = tp_constraint_gen G  (s, k) (* creates ref cells for evars *)
	    in
		matching_succeeds G (p, q)
	    end

	  | check_type con (G, TPi(OMIT,a,b)) = 
	    let 
		val plusconst = case con of
		 CON_LF => raise Error "TPi(OMIT) where a pure LF function type expected"
	       | CON_PLUS => true
	       | CON_MINUS => false
	    in
		check_type CON_LF (G,a) andalso
			     check_type con (ctxcons (a, G), b) andalso
			     Strict.check_strict_type plusconst b 
	    end
 
	  | check_type con (G, TPi(m,a,b)) = 
	    (case (con,m) of
		 (CON_LF, PLUS) => raise Error "TPi(PLUS) where a pure LF function type expected"
	       | _ => check_type CON_LF (G,a) andalso 
		      check_type con (ctxcons (a, G), b))
(* check a type spine *)
	and check_type' (G, Type, []) = true
	  | check_type' (G, KPi(_,a,k), m::s) = 
	    let
		val _ = if check_spinelt(G, m, a) then () else raise Error "argument type mismatch"
		val k' = subst_knd (TermDot(termof m,a,Id)) k
	    in
		check_type'(G,k',s)
	    end
	  | check_type' _ = false
	and synth (G, ARoot(Var n, s)) = synth'(G, ctxLookup(G, n), s)
	  | synth (G, ARoot(Const n, s)) = 
	    let
		 val b = case Sgn.classifier n of 
			     tclass b => b
			   | _ => raise Error "signature invariant violated!"
		 val (p, q, aopt) = constraint_gen G  (s, b, CG_SYNTH) (* creates ref cells for evars *)
(* DEBUG		 val _ = l3 := (p, q, aopt)::(!l3) *)
		 val _ = matching_succeeds G (p,q) (* raises Matching if not *)
	     in
		 Option.valOf aopt (* by invariant, aopt must be SOME *)
	     end
	  | synth (G, t as ERoot _) = elt_synth (G, eroot_elim_plus t)
	and synth' (G, a as TRoot(_,_), []) = a
	  | synth' (G, TPi(_,a,b), m::s) = 
	    let
		val _ = if check_spinelt(G, m, a) then () else raise Error "argument type mismatch"
		val b' = subst_tp (TermDot(termof m,a,Id)) b
	    in
		synth' (G, b', s)
	    end
	  | synth' _ = raise Error "applying nonfunction to argument"
	and elt_synth (G, AElt t) = synth (G, t)
	  | elt_synth (G, Ascribe(t,a)) = if check(G,NTerm t,a) then a else raise Error "ascription doesn't check"
	  | elt_synth (G, Elt _) = raise Error "trying to synthesize a merely checkable element"
	  | elt_synth (G, Omit) = raise Error "trying to synthesize an omitted argument"

	fun check_plusconst_type t = check_type CON_PLUS ([], t)
	fun check_minusconst_type t = check_type CON_MINUS ([], t)

(* check_strictness_type : bool -> tp -> bool

   For a type B = Pi x1 : A1 . Pi x2 : A2 ... a . S (where the Pis
   may be omit or plus or minus) 
   and plus_const : bool
   the call
   check_strictness_type plus_const B
   returns true iff for every i, the following holds:
     the variable xi has either a strict occurrence in Aj for
     some j > i where xj is bound by a plus-Pi, or else 
     plus_const = false and xi has a strict occurrence in a . S.

  This function does *not* check to make sure types such as A1
  do not contain omit-Pis and plus-Pis. This test is carried
  out in check_type. check_strictness_type is useful mainly when
  we are simply deciding, by trial and error, which of the arguments
  to B we should omit and which to force to be synthesizing.
 *)
	fun check_strictness_type _ (TRoot(n, s)) = true
	  | check_strictness_type plusconst (TPi(OMIT,_,b)) = 
	    check_strictness_type plusconst b andalso Strict.check_strict_type plusconst b 
	  | check_strictness_type plusconst (TPi(_,_,b)) = check_strictness_type plusconst b
							
	val check_plusconst_strictness = check_strictness_type true
	val check_minusconst_strictness = check_strictness_type false
end

