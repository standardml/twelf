(* Type Reconstruction *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Roberto Virga *)

(* ------------------------------------- *)
(* Translating Free Identifiers to EVars *)
(* ------------------------------------- *)

functor EVars (structure IntSyn' : INTSYN
               structure Names : NAMES
                 sharing Names.IntSyn = IntSyn')
  : VARS =
struct

  structure IntSyn = IntSyn'

  fun var (name, depth) =
      let
	val (X as IntSyn.EVar(_,_,V,_)) = Names.getEVar name
	val s = IntSyn.Shift depth
      in
	(IntSyn.EClo (V, s),
	 fn S => IntSyn.Redex (IntSyn.EClo (X, s), S))
      end
end;  (* functor EVars *)

(* ------------------------------------- *)
(* Translating Free Identifiers to FVars *)
(* ------------------------------------- *)

functor FVars (structure IntSyn' : INTSYN
               structure Names : NAMES
                 sharing Names.IntSyn = IntSyn')
  : VARS =
struct

  structure IntSyn = IntSyn'

  fun clearState () = ()

  fun var (name, depth) =
      let
	val V' = Names.getFVarType (name)
	val s = IntSyn.Shift (depth)
      in
        (IntSyn.EClo (V', s),
	 fn S => IntSyn.Root (IntSyn.FVar (name, V', s), S))
      end
end;  (* functor FVars *)

(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)

functor TpRecon (structure Global : GLOBAL
		 structure IntSyn' : INTSYN
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn'
		 structure Paths' : PATHS
		 structure Whnf : WHNF
		   sharing Whnf.IntSyn = IntSyn'
		 structure Unify : UNIFY
		   sharing Unify.IntSyn = IntSyn'
		 structure Abstract : ABSTRACT
		   sharing Abstract.IntSyn = IntSyn'
		 structure TypeCheck : TYPECHECK
		   sharing TypeCheck.IntSyn = IntSyn'
		 structure Strict : STRICT
		   sharing Strict.IntSyn = IntSyn'
		   sharing Strict.Paths = Paths'
		 structure Print : PRINT
		   sharing Print.IntSyn = IntSyn'
		 structure Timers : TIMERS
                 structure Vars : VARS 
                   sharing Vars.IntSyn = IntSyn'
                 structure CSManager : CS_MANAGER
                   sharing CSManager.IntSyn = IntSyn')
  : TP_RECON =
struct

  structure IntSyn = IntSyn'
  structure Paths = Paths'
  structure F = Print.Formatter
  type name = string

  (* Implementation of term and decl which are abstract in the parser.
     We write tm : term for the representation of a term tm and tm* :
     exp for its translation in internal syntax and d : dec for the
     representation of a declaration and d* : Dec for its translation
     into internal syntax.

     We write tm* @@ S for the result of appending spine S to the
     translation of tm.

     Invariants: If    tm (G, SS) = ((U, V), oc)
                 and   G |- tm* : tp*

                 then  G |- U : V  and  G |- V : L
                 and   ((S, V), os) = SS tp*
                 and   U = tm* @@ S

                 where oc = occurrence tree associated with U
                       os = occurrence spine associated with S

     raises exception Error if such a tp* does not exist
  *)
  type term = IntSyn.dctx * (IntSyn.Exp -> (IntSyn.Spine * IntSyn.Exp) * Paths.occSpine)
                -> (IntSyn.Exp * IntSyn.Exp) * Paths.occExp
  type dec = IntSyn.dctx -> IntSyn.Dec * Paths.occExp option	(* must be x:A where A:type *)

  (* Various error-related functions *)

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  fun joinRegions (oc1, oc2) = Paths.join (Paths.toRegion oc1, Paths.toRegion oc2)

  fun formatExp (G, U) =
      Print.formatExp (G, U)
      handle Names.Unprintable => F.String "%_unprintable_%"

  fun mismatchError (G, (V1', s), ((U2, V2), oc2), msg) =
      let
	val r = Paths.toRegion oc2
	val V1'fmt = formatExp (G, IntSyn.EClo (V1', s))
	val V2fmt = formatExp (G, V2)
	val diff = F.Vbox0 0 1
	           [F.String "Expected:", F.Space, V1'fmt, F.Break,
		    F.String "Found:   ", F.Space, V2fmt]
      in
	error (r, "Type mismatch\n"
	           ^ F.makestring_fmt diff ^ "\n"
	           ^ msg ^ "\n")
      end

  fun hasTypeError (G, (V1, oc1), (V2, oc2), msg) =
      let
	val r2 = Paths.toRegion oc2
	val V1fmt = formatExp (G, V1)
	val V2fmt = formatExp (G, V2)
	val diff = F.Vbox0 0 1
	           [F.String "Synthesized: ", V1fmt, F.Break,
		    F.String "Ascribed:    ", V2fmt]
      in
	error (r2, "Type ascription error\n"
	           ^ F.makestring_fmt diff ^ "\n"
	           ^ msg ^ "\n")
      end

  fun extraneousError (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.Space, V1fmt, F.Break,
			      F.String "is not a function type"]
	val r2 = Paths.toRegion oc2
      in
        error (r2, "Extraneous argument\n" ^ F.makestring_fmt nonFun ^ "\n")
      end

  (* nilSS --- empty spine and occurrence tree *)
  fun nilSS (V) = ((IntSyn.Nil, V), Paths.nils)

  (* Checking universe level restrictions *)
  fun checkUni (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
	 of (IntSyn.Uni(_), _) => ()
	  | _ => error (r, "Classifier is not a type or kind"))

  fun getUni (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
	 of (IntSyn.Uni (level), _) => level
          | _ => error (r, "Classifier is not a type or kind"))

  fun checkType (L, r) =
      (case Whnf.whnf (L, IntSyn.id)
         of (IntSyn.Uni (IntSyn.Type), _) => ()
          | _ => error (r, "Classifier is not a type"))

  (* Resolving identifier names *)

  (* findBVar (name, G)
      = SOME (k, V)  where G |- k : V and variable k is called name,
      = NONE  if no such k exists.
  *)
  fun findBVar (name, G) =
      let fun findBVar' (IntSyn.Null, k) = NONE
	    | findBVar' (IntSyn.Decl (G', IntSyn.Dec(NONE, _)), k) = findBVar' (G', k+1)
            | findBVar' (IntSyn.Decl (G', IntSyn.Dec(SOME(name'), V')), k) =
	      if name = name' then SOME(IntSyn.BVar(k),IntSyn.EClo(V',IntSyn.Shift(k)))
	      else findBVar' (G', k+1)
      in
	findBVar' (G, 1)
      end

  (* findConst (name)
      = SOME (c, i, V) where  c : V and c has i implicit arguments, c is called name
      = NONE  if so such c exists.
  *)
  fun findConst (name) =
      (case Names.nameLookup (name)
	 of NONE => (case CSManager.parse (name)
                       of NONE => NONE
                        | SOME(cs, conDec) => SOME (IntSyn.FgnConst (cs, conDec), conDec))
          | SOME(cid) => (case IntSyn.sgnLookup(cid)
			    of (conDec as IntSyn.ConDec _) => SOME(IntSyn.Const(cid), conDec)
			     | (conDec as IntSyn.ConDef _) => SOME(IntSyn.Def(cid), conDec)
                             | (conDec as IntSyn.AbbrevDef _) => SOME(IntSyn.NSDef(cid), conDec)))

  (* Translating identifiers once they have been classified *)
  (* as constant, bound variable, or free variable *)

  (* Constant *)
  fun const ((H, conDec), r, (G, SS)) =
      let
        val i = IntSyn.conDecImp (conDec)

	fun supplyImplicit (0, (V', s)) = SS (IntSyn.EClo(V', s))
	  | supplyImplicit (i, (IntSyn.Pi ((IntSyn.Dec (x, V1), _), V2), s)) =
	    let
	      val U1 = IntSyn.newEVar (G, IntSyn.EClo(V1, s))
	      val ((S2, V), os) =
		     supplyImplicit (i-1, Whnf.whnf (V2, IntSyn.Dot(IntSyn.Exp(U1), s)))
	    in
	      ((IntSyn.App (U1, S2), V), os)
	    end
	val ((S, V), os) = supplyImplicit (i, Whnf.whnf (IntSyn.conDecType (conDec),
                                                         IntSyn.id))

        fun makeForeign (IntSyn.Foreign (cs, toForeign), (H, S)) = toForeign S
          | makeForeign (_, (H, S)) = IntSyn.Root (H, S)
        val U = makeForeign (IntSyn.conDecStatus (conDec), (H, S))
      in
	((U, V), Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, i, os))
      end

  (* Bound variable *)
  fun bvar ((n, V'), r, SS) =
      let
	val ((S, V), os) = SS V'
      in
	((IntSyn.Root (n, S), V),
	 Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, 0, os))
      end

  (* Free variable *)
  (* Translated to FVar in declarations, to EVar in queries *)
  fun var (name, r, depth, SS) =
      let
        val (V', H) = Vars.var (name, depth)
	val ((S, V), os) = SS V'
      in
	((H S, V),
	 Paths.root (Paths.toRegionSpine (os, r), Paths.leaf r, 0, os))
      end

  (* The remaining functions appear in the interface *)

  (* Resolving lower-case, upper-case or quoted identifiers *)
  (* lcid -- lower case identifier *)
  fun lcid (name, r) (G, SS) =
      (case findBVar (name, G)
	 of NONE => (case findConst (name)
		       of NONE => error (r, "Undeclared constant " ^ name)
			| SOME info => (const (info, r, (G, SS))))
          | SOME nV => bvar (nV, r, SS))

  (* ucid -- upper case identifier *)
  fun ucid (name, r) (G, SS) =
      (case findBVar (name, G)
	 of NONE => (case findConst (name)
		       of NONE => var (name, r, IntSyn.ctxLength G, SS)
			| SOME info => const (info, r, (G, SS)))
	  | SOME nV => bvar (nV, r, SS))

  (* quid -- quoted identifier *)
  (* currently not used *)
  fun quid (name,r) (G, SS) =
      (case findConst (name)
	 of NONE => error (r, "Undeclared quoted constant " ^ name)
	  | SOME info => const (info, r, (G, SS)))

  (* scon -- string constants *)
  fun scon (name,r) (G, SS) =
      (case findConst (name)
         of NONE => error (r, "Strings unsupported in current signature")
          | SOME info => const (info, r, (G, SS)))

  (* Application "tm1 tm2" *)
  fun app (tm1, tm2) (G, SS) =
        (* argument first or function first? Here: function first *)
        tm1 (G, fn V1 => app2 (tm2) (G, SS) (V1))

  and app2 (tm2) (G, SS) (V1) =
         (* convert tm2 early to obtain error location *)
         app2' (tm2 (G, nilSS)) (G, SS) (V1)

  and app2' (UV2 as ((U2, V2), oc2)) (G, SS) (V1) =
      (case Whnf.whnf (V1, IntSyn.id)
	 of (IntSyn.Pi ((IntSyn.Dec (x, V1'), P), V1''), s) =>
	    let
	      val _ = Unify.unify (G, (V1', s), (V2, IntSyn.id))
		      handle Unify.Unify(msg) => mismatchError (G, (V1', s), UV2, msg)
	      val ((S, V), os) = SS (IntSyn.EClo (V1'', Whnf.dotEta (IntSyn.Exp(U2), s)))
	    in
	      ((IntSyn.App (U2, S), V), Paths.app (oc2, os))
	    end
	  | (V1, s) =>
	    let
	      val V1' = IntSyn.newTypeVar (G)
	      val D' = IntSyn.Dec (NONE, V1')
	      val V1'' = IntSyn.newTypeVar (IntSyn.Decl (G, D'))
	      (* Invariant: type families are always constants and *)
	      (* therefore of known kind.  In case tm1 is a type family *)
	      (* the other case (V1 = Pi x:A. K) applies *)
	      val V = IntSyn.Pi ((D', IntSyn.Maybe), V1'')
	    in
	      Unify.unify (G, (V1, s), (V, IntSyn.id))
	      handle Unify.Unify (msg) => extraneousError (G, (V1, s), (U2, oc2));
	      (* now, first case must apply *)
	      app2' (UV2) (G, SS) (V)
	    end)

  (* Non-dependent function type "tm1 -> tm2" *)
  fun arrow (tm1, tm2) (G, SS) =
      let
	val ((V1, L1), oc1) = tm1 (G, nilSS)
	val _ = checkType (L1, Paths.toRegion oc1)
	val D1 = IntSyn.Dec (NONE, V1)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val r = joinRegions (oc1, oc2)
      in
	case SS L2
	  of ((IntSyn.Nil, L2'), _) =>
	      ((IntSyn.Pi ((D1, IntSyn.No), IntSyn.EClo(V2,IntSyn.shift)), L2),
	       Paths.bind (r, SOME(oc1), oc2))
	   (* can the next case arise? *)
	   | ((S, V'), _) => error (r, "function type applied to argument")
      end

  (* Non-dependent function type "tm2 <- tm1" *)
  fun backarrow (tm2, tm1) (G, SS) =
        arrow (tm1, tm2) (G, SS)

  (* Explicit type ascription "tm1 : tm2" *)
  fun hastype (tm1, tm2) (G, SS) =
      let
	val ((U1, V1), oc1) = tm1 (G, nilSS)
	val ((V2, L2), oc2) = tm2 (G, nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val _ = Unify.unify (G, (V1, IntSyn.id), (V2, IntSyn.id))
	        handle Unify.Unify(msg) => hasTypeError (G, (V1, oc1), (V2, oc2), msg)
      (* regions apply only to normal forms: errors in type ascriptions are hard *)
      (* to trace -- V2 and oc2 are ignored below. -fp *)
      in
	case SS V2
	  of ((IntSyn.Nil, _), _) => ((U1, V2), oc1)
	   | ((S, V'), os) =>
	      ((IntSyn.Redex (U1, S), V'),
	       Paths.root (Paths.toRegionSpine (os, Paths.toRegion oc1), oc1, 0, os))
      end

  (* Omitted objects (from underscore) "_" *)
  fun omitobj (r) (G, SS) =
      let
	val V = IntSyn.newTypeVar (G)
	val X = IntSyn.newEVar (G, V)
      in
	  case SS V
	    of ((IntSyn.Nil, V'), _) => ((X, V), Paths.leaf r) (* V = V' *)
	     | ((S, V'), _) => ((IntSyn.Redex (X, S), V'), Paths.leaf r)
      end

  (* Omitted types (from definitions) *)
  fun omittyp (r) (G, SS) =
      let
	val X = IntSyn.newTypeVar (G)
      in
	case SS (IntSyn.Uni (IntSyn.Type))
	  of ((IntSyn.Nil, L), _) => ((X, L), Paths.leaf r) (* L = type *)
	   | (S, V') => error (r, "omitted type applied to argument")
      end

  (* Dependent function type "{id:tm} tm" where dec = "id:tm" *)
  fun pi (dec, tm, r1) (G, SS) =
      let
	val (D1 as IntSyn.Dec (x, V1), oc1Opt) = dec G
	val ((V2, L2), oc2) = tm (IntSyn.Decl (G, D1), nilSS)
	val _ = checkUni (L2, Paths.toRegion oc2)
	val r = Paths.join (r1, Paths.toRegion oc2)
      in
	case SS L2
	  of ((IntSyn.Nil, L2'), _) =>
	       ((IntSyn.Pi ((D1, IntSyn.Maybe), V2), L2), (* L2 = L2' *)
	        Paths.bind (r, oc1Opt, oc2))
	   (* can the next case arise? *)
	   | (S, V') => error (r, "dependent function type applied to argument")
      end

  (* Lambda abstraction "[id:tm] tm" where dec = "id:tm" *)
  fun lam (dec, tm, r1) (G, SS) =
      let
	val (D1 as IntSyn.Dec (x, V1), oc1Opt) = dec G
	val ((U2, V2), oc2) = tm (IntSyn.Decl (G, D1), nilSS)
	val ((S, V), os) = SS (IntSyn.Pi ((D1, IntSyn.Maybe), V2))
	val r = Paths.join (r1, Paths.toRegion oc2)
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Lam (D1, U2), V),
			    Paths.bind (r, oc1Opt, oc2))
	   | _ => ((IntSyn.Redex (IntSyn.Lam (D1, U2), S), V),
		   (* mismatch here *)
		   (Paths.root (Paths.toRegionSpine (os, r),
				Paths.bind (r, oc1Opt, oc2), 0, os)))
      end

  (* Type "type" *)
  fun typ (r) (G, SS) =
      let
	val ((S, V), os) = SS (IntSyn.Uni (IntSyn.Kind))
      in
	case S
	  of IntSyn.Nil => ((IntSyn.Uni (IntSyn.Type), V), Paths.leaf r)
	   (* can the next case arise? *)
	   | _ => error (r, "`type' applied to argument")
      end

  (* Declarations "id:tm" *)
  fun dec (x, tm) (G) =
      let
	val ((V, L), oc) = tm (G, nilSS)
	val _ = checkType (L, Paths.toRegion (oc))
      in
	(IntSyn.Dec (x, V), SOME(oc))
      end

  (* Declarations with implicit type "id" *)
  fun dec0 (x) (G) =
      let
	val V = IntSyn.newTypeVar (G)
      in
	(IntSyn.Dec (x, V), NONE)
      end

  (* Constant declarations *)
  datatype condec =
      condec of name * term
    | condef of name option * term * term option

  (* Queries, with optional proof term variable *)
  datatype query =
      query of name option * term

  (* Converting a term to an expression in a context *)
  (* Check that the expression is a valid type *)
  (* Throws away the associated occurrence tree *)
  fun termToExp (G, tm) =
      let
	val ((V, L), oc) = tm (G, nilSS)
	val _ = checkType (L, Paths.toRegion oc)
      in
	V
      end

  (* Converting a declaration to an expression in a context *)
  (* Throws away the associated occurrence tree *)
  fun decToDec (G, dec) =
      let
	val (D, ocOpt) = dec G
      in
	D
      end
  
  (* termToExp0 (tm) = ((U,V), oc) 
     where . |- U : V
  *)
  fun termToExp0 (tm) = tm (IntSyn.Null, nilSS)

  (* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)
  fun freeVar (SOME(name), Xs) =
        List.exists (fn (_, name') => name = name') Xs
    | freeVar _ = false

  (* inferLevel (V) = L
     Invariant: . |- V : L, V nf
     (V must be a valid classifier, that is, a type or kind)
  *)
  fun inferLevel (IntSyn.Pi (_, V')) = inferLevel V'
    | inferLevel (IntSyn.Root _) = IntSyn.Type
    | inferLevel (IntSyn.Uni _) = (* V = type *) IntSyn.Kind
    (* no other cases by invariant *)

  (* queryToQuery (q) = (V, XOpt, [(X1,"X1"),...,(Xn,"Xn")])
     where XOpt is the optional proof term variable
           X1,...,Xn are the free EVars in the terms with their names

     Free variables in q are interpreted existentially (as EVars).

     Only works properly when the Vars parameter structure
     is instantiated to EVars, not FVars.
  *)
  (* call TypeCheck... if !doubleCheck = true? *)
  (* Wed May 20 08:00:28 1998 -fp *)
  fun queryToQuery (query (optName, tm), Paths.Loc (fileName, r)) = 
      let
	val _ = Names.varReset ()
	val ((V,L), oc) = (Timers.time Timers.recon termToExp0) tm
	val _ = checkType (L, Paths.toRegion oc)
	val Xs = Names.namedEVars ()
	val _ = if freeVar (optName, Xs)
		  then error (Paths.toRegion oc,
			      "Proof term variable " ^ valOf optName
			      ^ " occurs in type\n")
		else ()
      in
	(V, optName, Xs)
      end

  (* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the Vars parameter structure is
     instantiated to FVars, not EVars.
  *)
  (* should printing of result be moved to frontend? *)
  (* Wed May 20 08:08:50 1998 -fp *)
  fun condecToConDec (condec(name, tm), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset ()
	val ((V, L), oc) = (Timers.time Timers.recon termToExp0) tm
	val level = getUni (L, Paths.toRegion oc)
        val (i, V') = (Timers.time Timers.abstract Abstract.abstractDecImp) V
	                handle Abstract.Error (msg)
			       => raise Abstract.Error (Paths.wrap (r, msg))
	val cd = Names.nameConDec (IntSyn.ConDec (name, i, IntSyn.Normal, V', level))
	val ocd = Paths.dec (r, i, oc)
	val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni (level)) 
		else ()
      in
	(SOME(cd), SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, SOME(tm2)), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset ()
	val ((V, L), oc2) = (Timers.time Timers.recon termToExp0) tm2
	val level = getUni (L, Paths.toRegion oc2)
	val ((U, V'), oc1) = (Timers.time Timers.recon termToExp0) tm1
	val _ = (Timers.time Timers.recon Unify.unify) (IntSyn.Null, (V', IntSyn.id), (V, IntSyn.id))
	        handle Unify.Unify (msg) => hasTypeError (IntSyn.Null, (V', oc1), (V, oc2), msg)
	val (i, (U'', V'')) =
	        (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
		handle Abstract.Error (msg)
		          => raise Abstract.Error (Paths.wrap (r, msg))
	val name = case optName of NONE => "_" | SOME(name) => name
	val ocd = Paths.def (r, i, oc1, SOME(oc2))
        val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, i, U'', V'', level))
		 else (case level
			 of IntSyn.Kind => error (r, "Type families cannot be defined, only objects")
		          | _ => ();
		       Strict.check ((U'', V''), SOME(ocd));
		       Names.nameConDec (IntSyn.ConDef (name, i, U'', V'', level)))
        val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni (level));
			(Timers.time Timers.checking TypeCheck.check) (U'', V''))
		else ()
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, NONE), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset ()
	val ((U, V), oc1) = (Timers.time Timers.recon termToExp0) tm1
	val (i, (U'', V'')) =
	        (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
		handle Abstract.Error (msg)
		          => raise Abstract.Error (Paths.wrap (r, msg))
	val level = inferLevel V''
	val name = case optName of NONE => "_" | SOME(name) => name
	val ocd = Paths.def (r, i, oc1, NONE)
        val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, i, U'', V'', level))
		 else (case level
			 of IntSyn.Kind => error (r, "Type families cannot be defined, only objects")
		          | _ => ();
		       Strict.check ((U'', V''), SOME(ocd));
		       Names.nameConDec (IntSyn.ConDef (name, i, U'', V'', level)))
        val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni (level));
			(Timers.time Timers.checking TypeCheck.check) (U'', V''))
		else ()
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end

end; (* functor TpRecon *)
