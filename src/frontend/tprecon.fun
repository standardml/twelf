(* Type Reconstruction with Tracing *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow, Roberto Virga, Kevin Watkins *)

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

  structure TermSyn =
  struct

    datatype Class =
      Term
    | Type of IntSyn.Exp
    | Kind of IntSyn.Exp

    (* Terms annotated with approximate types *)

    datatype Term =
      Typ of Paths.region
    | Lam of Dec * Term * Paths.region
    | Arrow of Term * Term
    | Pi of Dec * Term * Paths.region
    | Omitobj of IntSyn.Exp * Paths.region
    | Implicit of IntSyn.Exp * Paths.region
    | Hastype of Term * Term
    | Root of Head * Spine
    | Redex of Term * Spine

    and Head =
      EVar of string * Paths.region
    | FVar of string * Paths.region
    | BVar of int * Paths.region
    | Const of IntSyn.Head * IntSyn.ConDec * Paths.region

    and Spine =
      Nil
    | App of Term * Spine

    and Dec = Dec of name option * Term option * IntSyn.Exp

  end

  type approxDec = TermSyn.Dec
  type approxExp = TermSyn.Term
  type approxCtx = approxDec IntSyn.Ctx

  type term = approxCtx * bool -> TermSyn.Term
  type dec = approxCtx * bool -> TermSyn.Dec

  (* Various error-related functions *)

  exception Error of string
  (* fun error (r, msg) = raise Error (Paths.wrap (r, msg)) *)
  val errorCount = ref 0
  val errorFileName = ref "no file"

  val errorThreshold : int option ref = ref (SOME (0))
  fun exceeds (i, NONE) = false
    | exceeds (i, SOME(j)) = i > j

  fun resetErrors (fileName) =
      (errorCount := 0;
       errorFileName := fileName)

  fun checkErrors (r) =
      if !errorCount > 0
	then raise Error (" " ^ Int.toString (!errorCount)
			  ^ " error" ^ (if !errorCount > 1 then "s" else "")
			  ^ " found")
      else ()

  fun error (r, msg) =
      (errorCount := !errorCount + 1;
       print (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       if exceeds (!errorCount, !errorThreshold)
	 then checkErrors (r)
       else ();
       ())

  (* Resolving identifier names *)

  (* findBVar (name, G)
      = SOME (k, V)  where G |- k : V and variable k is called name,
      = NONE  if no such k exists.
  *)
  fun findBVar (name, Ga) =
      let fun findBVar' (IntSyn.Null, k) = NONE
	    | findBVar' (IntSyn.Decl (Ga', TermSyn.Dec (NONE, _, _)), k) = findBVar' (Ga', k+1)
            | findBVar' (IntSyn.Decl (Ga', TermSyn.Dec (SOME(name'), _, _)), k) =
	      if name = name' then SOME(k)
	      else findBVar' (Ga', k+1)
      in
	findBVar' (Ga, 1)
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
  fun const ((H, conDec), r) =
      let
        fun supplyImplicit (0) = TermSyn.Nil
          | supplyImplicit (i) =
              TermSyn.App (TermSyn.Implicit (IntSyn.newTypeVar (IntSyn.Null), r),
                           supplyImplicit (i-1))
      in
        TermSyn.Root (TermSyn.Const (H, conDec, r),
                      supplyImplicit (IntSyn.conDecImp (conDec)))
      end

  (* Bound variable *)
  fun bvar (n, r) = TermSyn.Root (TermSyn.BVar (n, r), TermSyn.Nil)

  (* Free variable *)
  (* Translated to FVar in declarations, to EVar in queries *)
  fun var (name, r, true) =
      let
        val _ = Names.getEVar name (* get the variable into the Names
                                      table before we do any printing *)
      in
        TermSyn.Root (TermSyn.EVar (name, r), TermSyn.Nil)
      end
    | var (name, r, false) =
      let
        val _ = Names.getFVarType name (* get the variable into the Names
                                          table before we do any printing *)
      in
        TermSyn.Root (TermSyn.FVar (name, r), TermSyn.Nil)
      end

  (* The remaining functions appear in the interface *)

  (* Resolving lower-case, upper-case or quoted identifiers *)
  (* lcid -- lower case identifier *)
  fun lcid (name, r) (Ga, qf) =
      (case findBVar (name, Ga)
	 of NONE => (case findConst (name)
		       of NONE => (error (r, "Undeclared constant " ^ name);
				   (* translate to FVar or EVar *)
				   var (name, r, qf))
			| SOME info => (const (info, r)))
          | SOME n => bvar (n, r))

  (* ucid -- upper case identifier *)
  fun ucid (name, r) (Ga, qf) =
      (case findBVar (name, Ga)
	 of NONE => (case findConst (name)
		       of NONE => var (name, r, qf)
			| SOME info => const (info, r))
	  | SOME n => bvar (n, r))

  (* quid -- quoted identifier *)
  (* currently not used *)
  fun quid (name, r) (Ga, qf) =
      (case findConst (name)
	 of NONE => (error (r, "Undeclared quoted constant " ^ name);
		     (* translate to FVar or EVar *)
		     var (name, r, qf))
	  | SOME info => const (info, r))

  (* scon -- string constants *)
  fun scon (name,r) (Ga, qf) =
      (case findConst (name)
         of NONE => (error (r, "Strings unsupported in current signature");
		     (* translate to FVar or EVar *)
		     var (name, r, qf))
          | SOME info => const (info, r))

  fun spineAppend (TermSyn.Nil, Ua) =
        TermSyn.App (Ua, TermSyn.Nil)
    | spineAppend (TermSyn.App (Ua1, Ua2), Ua3) =
        TermSyn.App (Ua1, spineAppend (Ua2, Ua3))

  (* Application "tm1 tm2" *)
  fun app (tm1, tm2) (Ga, qf) =
      (case tm1 (Ga, qf)
         of TermSyn.Root (hd, sp) =>
              TermSyn.Root (hd, spineAppend (sp, tm2 (Ga, qf)))
          | TermSyn.Redex (tm, sp) =>
              TermSyn.Redex (tm, spineAppend (sp, tm2 (Ga, qf)))
          | tm1 => TermSyn.Redex (tm1, TermSyn.App (tm2 (Ga, qf), TermSyn.Nil)))

  (* Non-dependent function type "tm1 -> tm2" *)
  fun arrow (tm1, tm2) (Ga, qf) = TermSyn.Arrow (tm1 (Ga, qf), tm2 (Ga, qf))

  (* Non-dependent function type "tm2 <- tm1" *)
  fun backarrow (tm2, tm1) (Ga, qf) = arrow (tm1, tm2) (Ga, qf)

  (* Explicit type ascription "tm1 : tm2" *)
  fun hastype (tm1, tm2) (Ga, qf) = TermSyn.Hastype (tm1 (Ga, qf), tm2 (Ga, qf))

  (* Omitted objects (from underscore) "_" *)
  fun omitobj (r) (Ga, qf) = TermSyn.Omitobj (IntSyn.newTypeVar (IntSyn.Null), r)

  (* Dependent function type "{id:tm} tm" where dec = "id:tm" *)
  fun pi (dec, tm, r) (Ga, qf) =
      let
        val Da = dec (Ga, qf)
      in
        TermSyn.Pi (Da, tm (IntSyn.Decl (Ga, Da), qf), r)
      end

  (* Lambda abstraction "[id:tm] tm" where dec = "id:tm" *)
  fun lam (dec, tm, r) (Ga, qf) =
      let
        val Da = dec (Ga, qf)
      in
        TermSyn.Lam (Da, tm (IntSyn.Decl (Ga, Da), qf), r)
      end

  (* Type "type" *)
  fun typ (r) (Ga, qf) = TermSyn.Typ (r)

  (* Declarations "id:tm" *)
  fun dec (x, tm) (Ga, qf) =
        TermSyn.Dec (x, SOME (tm (Ga, qf)), IntSyn.newTypeVar (IntSyn.Null))

  (* Declarations with implicit type "id" *)
  fun dec0 (x) (Ga, qf) =
        TermSyn.Dec (x, NONE, IntSyn.newTypeVar (IntSyn.Null))

  fun joinRegions (oc1, oc2) = Paths.join (Paths.toRegion oc1, Paths.toRegion oc2)

  (* ------------------------------------------------------------------------ *)
  (* Begin tracing code *)

  val trace = ref false

  fun evarsToString (Xnames) =
      let
	val inst = Print.evarInstToString (Xnames)
	val constrOpt = Print.evarCnstrsToStringOpt (Xnames)
      in
	case constrOpt
	  of NONE => inst
	   | SOME(constr) => inst ^ "\nConstraints:\n" ^ constr
      end
      handle Names.Unprintable => "%_unifier unprintable_%"

  fun formatExp (G, U) =
      Print.formatExp (G, U)
      handle Names.Unprintable => F.String "%_unprintable_%"

  fun shape (V1, V2) = Unify.shape (V1, V2)
      (*
      if not (!trace) then Unify.shape (V1, V2)
      else 
      let 
	val eqnsFmt = F.HVbox [F.String "|~?", F.Space, Print.formatExp (IntSyn.Null, V1),
			       F.Break, F.String "=", F.Space, Print.formatExp (IntSyn.Null, V2)]
	val _ = print (F.makestring_fmt eqnsFmt ^ "\n")
	val _ = Unify.shape (V1, V2)
	val eqnsFmt = F.HVbox [F.String "|~", F.Space, Print.formatExp (IntSyn.Null, V1),
			       F.Break, F.String "=", F.Space, Print.formatExp (IntSyn.Null, V2)]
	val _ = print (F.makestring_fmt eqnsFmt ^ "\n")
      in
	()
      end
      *)

  fun unify (G, (V1, s1), (V2, s2)) =
      if not (!trace) then Unify.unify (G, (V1, s1), (V2, s2))
      else 
      let 
	val Xs = Abstract.collectEVars (G, (V2, s2), Abstract.collectEVars (G, (V1, s1), nil))
	val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
	val eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, IntSyn.EClo (V1, s1)),
			       F.Break, F.String "=", F.Space, formatExp (G, IntSyn.EClo (V2, s2))]
	val _ = print (F.makestring_fmt eqnsFmt ^ "\n")
	val _ = Unify.unify (G, (V1, s1), (V2, s2))
	val _ = print (evarsToString (Xnames) ^ "\n")
      in
	()
      end

  fun showInferred (G, ((U, V), oc)) =
      if not (!trace) then ()
      else 
      let
	val Xs = Abstract.collectEVars (G, (U, IntSyn.id),
					Abstract.collectEVars (G, (V, IntSyn.id), nil))
	val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
	val jFmt = F.HVbox [F.String "|-", F.Space, formatExp (G, U), F.Break,
			    F.String ":", F.Space, formatExp (G, V)]
	val _ = print (F.makestring_fmt jFmt ^ "\n")
      in
	()
      end
      

  (* End tracing code *)
  (* ------------------------------------------------------------------------ *)

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
	           ^ msg)
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
	           ^ msg)
      end

  fun extraneousError (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.Space, V1fmt, F.Break,
			      F.String "is not a function type"]
	val r2 = Paths.toRegion oc2
      in
        error (r2, "Extraneous argument\n" ^ F.makestring_fmt nonFun)
      end

  fun ambiguousError (G, V, r, msg) =
      let
        val Vfmt = formatExp (G, V)
        val amb = F.HVbox [F.String "Reconstructed:", F.Space, Vfmt, F.Break,
                           F.String "contains type variables"]
      in
        error (r, msg ^ F.makestring_fmt amb)
      end

  fun whnfApprox (V) =
      let
        val (V', s) = Whnf.whnf (V, IntSyn.id)
      in
        V'
      end

  (* Checking universe level restrictions *)
  fun checkUni (La, r, msg) =
      (case whnfApprox (La)
         of (IntSyn.Uni (_)) => ()
          | _ => error (r, msg))

  fun checkType (La, r, msg) =
      (case whnfApprox (La)
         of (IntSyn.Uni (IntSyn.Type)) => ()
          | _ => error (r, msg))

  fun getUni (La, r, msg) =
      (case whnfApprox (La)
	 of (IntSyn.Uni (level)) => level
          | _ => (error (r, msg); IntSyn.Type))

  fun decl (G, D) = IntSyn.Decl (G, Names.decLUName (G, D))

  (* precondition: . |- V : L *)

  fun makeApproxW (IntSyn.Uni (IntSyn.Type)) =
        (IntSyn.Uni (IntSyn.Type), true)
    | makeApproxW (IntSyn.Pi ((D1, P), V2)) =
      let
        val Da1 = makeApproxDec (D1)
        val (Va2, isType) = makeApprox (V2)
      in
        (IntSyn.Pi ((Da1, P), Va2), isType)
      end
    | makeApproxW (IntSyn.Root (H, S)) =
        (IntSyn.Root (H, IntSyn.Nil), false)

  and makeApprox (V) = makeApproxW (whnfApprox (V))

  and makeApproxDec (IntSyn.Dec (x, V)) =
      let
        val (Va, C) = makeApprox (V)
        (* C = false *)
      in
        IntSyn.Dec (x, Va)
      end

  fun ensurePiApprox (Va) =
      (case whnfApprox (Va)
         of (IntSyn.Pi ((IntSyn.Dec (x, Va1), P), Va2)) =>
              (Va1, Va2)
          | (Va) => 
            let
              val Va1 = IntSyn.newTypeVar (IntSyn.Null)
              val Da1 = IntSyn.Dec (NONE, Va1)
              val Va2 = IntSyn.newTypeVar (IntSyn.Null)
            in
              shape (Va, IntSyn.Pi ((Da1, IntSyn.Maybe), Va2))
              handle Unify.Unify msg => ();
              (Va1, Va2)
            end)

  (* Check that a term is approximately well-typed, and return
     the approximate type and the level. *)

  fun approxReconShow (Ga, Ua) = approxRecon (Ga, Ua)

  and approxRecon (Ga, TermSyn.Typ (r)) =
        (SOME (IntSyn.Uni IntSyn.Type), IntSyn.Uni IntSyn.Kind, r)
    | approxRecon (Ga, TermSyn.Lam (Da1 as TermSyn.Dec (x, _, Va1), t2, r)) =
      let
        val r1Opt = approxReconDec (Ga, Da1)
        val (Ua2, Va2, r2) = approxReconShow (IntSyn.Decl (Ga, Da1), t2)
        val _ = case Ua2
                  of NONE => ()
                   | SOME _ => error (r2, "Body of abstraction is not at term level")
      in
        (NONE, IntSyn.Pi ((IntSyn.Dec (x, Va1), IntSyn.Maybe), Va2),
         Paths.join (r, r2))
      end
    | approxRecon (Ga, TermSyn.Arrow (t1, t2)) =
      let
        val (Va1, La1, r1) = approxReconShow (Ga, t1)
        val _ = checkType (La1, r1, "Domain of function is not a type")
        val (Va2, La2, r2) = approxReconShow (Ga, t2)
        val _ = checkUni (La2, r2, "Range of function is not a type or kind")
      in
        (SOME (IntSyn.Pi ((IntSyn.Dec (NONE, Option.valOf Va1), IntSyn.No),
                          Option.valOf Va2)), La2, Paths.join (r1, r2))
      end
    | approxRecon (Ga, TermSyn.Pi (Da1 as TermSyn.Dec (x, _, Va1), t2, r)) =
      let
        val _ = approxReconDec (Ga, Da1)
        val (Va2, La2, r2) = approxReconShow (IntSyn.Decl (Ga, Da1), t2)
        val _ = checkUni (La2, r2, "Range of function is not a type or kind")
      in
        (SOME (IntSyn.Pi ((IntSyn.Dec (x, Va1), IntSyn.Maybe),
                          Option.valOf Va2)), La2, Paths.join (r, r2))
      end
    | approxRecon (Ga, TermSyn.Omitobj (Va, r)) =
        (NONE, Va, r)
    | approxRecon (Ga, TermSyn.Implicit (Va, r)) =
        (NONE, Va, r)
    | approxRecon (Ga, TermSyn.Hastype (t1, t2)) =
      let
        val (Ua1, Va1, r1) = approxReconShow (Ga, t1)
        val (Va2, La2, r2) = approxReconShow (Ga, t2)
        val uni = getUni (La2, r2, "Classifier in ascription is not a type or kind")
        val _ = case (Ua1, uni)
                  of (NONE, IntSyn.Type) => ()
                   | (SOME _, IntSyn.Kind) =>
                       checkType (Va1, r1, "Ascription applied to object at invalid level")
                   | _ => error (r1, "Ascription applied to object at invalid level")
      in
        shape (Va1, Option.valOf Va2)
        handle Unify.Unify msg => ();
        (* use ascribed type if unification failed *)
        (Ua1, Option.valOf Va2, r1)
      end
    | approxRecon (Ga, TermSyn.Root (hd, sp)) =
      let
        val (Ua, Va, r) = approxReconHead (Ga, hd)
        val (Va', r') = approxReconSpine (Ga, Va, r, sp)
      in
        (Ua, Va', r')
      end
    | approxRecon (Ga, TermSyn.Redex (Ua, sp)) =
      let
        val (Ua, Va, r) = approxReconShow (Ga, Ua)
        val (Va', r') = approxReconSpine (Ga, Va, r, sp)
      in
        (Ua, Va', r')
      end

  and approxReconHead (Ga, TermSyn.EVar (name, r)) =
      let
        val (U, Va, set) = Names.getEVar (name)
      in
        (NONE, Va, r)
      end
    | approxReconHead (Ga, TermSyn.FVar (name, r)) =
      let
        val (V, Va, set) = Names.getFVarType (name)
      in
        (NONE, Va, r)
      end
    | approxReconHead (Ga, TermSyn.BVar (n, r)) =
      let
        val (TermSyn.Dec (_, _, Va)) = IntSyn.ctxLookup (Ga, n)
      in
        (NONE, Va, r)
      end
    | approxReconHead (Ga, TermSyn.Const (H, condec, r)) =
      let
        val (Va, isType) = makeApprox (IntSyn.conDecType (condec))
      in
        (if isType then SOME (IntSyn.Root (H, IntSyn.Nil))
         else NONE, Va, r)
      end

  and approxReconSpine (Ga, Va, r, TermSyn.Nil) = (Va, r)
    | approxReconSpine (Ga, Va, r, TermSyn.App (t, sp)) =
      let
        val (Ua1, Va1, r1) = approxReconShow (Ga, t)
        val _ = case Ua1
                  of NONE => ()
                   | _ => error (r1, "Argument to function is not at term level")
        val (Va1', Va2') = ensurePiApprox (Va)
      in
        shape (Va1, Va1')
        handle Unify.Unify msg => ();
        approxReconSpine (Ga, Va2', Paths.join (r, r1), sp)
      end

  and approxReconDec (Ga, TermSyn.Dec (name, tOpt, Va1)) =
      (case tOpt
         of SOME t =>
            let
              val (Va, La, r) = approxReconShow (Ga, t)
              val _ = checkType (La, r, "Classifier in declaration is not a type")
            in
              (* should never fail *)
              shape (Option.valOf Va, Va1)
              handle Unify.Unify msg => ();
              SOME (r)
            end
          | NONE => NONE)

  (* newLoweredEVar (G, (V, s)) = U
     Make a new lowered EVar.

     if G |- s : G1  and  G1 |- V : type
     then G |- U : V[s] *)

  fun newLoweredEVarW (G, (IntSyn.Pi ((D1, dp), V2), s)) =
      let
        val D1' = IntSyn.decSub (Names.decLUName (G, D1), s)
      in
        IntSyn.Lam (D1', newLoweredEVar (IntSyn.Decl (G, D1'), (V2, IntSyn.dot1 s)))
      end
    | newLoweredEVarW (G, (V, s)) =
        IntSyn.newEVar (G, IntSyn.EClo (V, s))

  and newLoweredEVar (G, Vs) = newLoweredEVarW (G, Whnf.whnf Vs)

  (* newSpineVar (G, (V, s)) = S
     Make a new spine of variables given the kind of the head
     (which will be a type family).

     if G |- s : G1  and  G1 |- V : kind
     then G |- S : V > a *)

  fun newSpineVarW (G, (IntSyn.Uni _, s)) = IntSyn.Nil
    | newSpineVarW (G, (IntSyn.Pi ((IntSyn.Dec (_, V1), _), V2), s)) =
      let
        val U1 = newLoweredEVar (G, (V1, s))
        (* IntSyn.Dot instead of Whnf.dotEta? -kw *)
        val S2 = newSpineVar (G, (V2, Whnf.dotEta (IntSyn.Exp U1, s)))
      in
        IntSyn.App (U1, S2)
      end

  and newSpineVar (G, Vs) = newSpineVarW (G, Whnf.whnf Vs)

  (* approxToTypeVar1 (G, Va) = (V, gr)
     Make a type variable based on its approximation.

     if |~ Va : type  and  G ctx
     then G |- V : type  and  V ~~ Va
      and gr = true  iff  V contains no type variables *)

  fun approxToTypeVar1W (G, IntSyn.Pi ((IntSyn.Dec (x, Va1), dp), Va2)) =
      let
        val (V1, gr1) = approxToTypeVar1 (G, Va1)
        val D1 = Names.decLUName (G, IntSyn.Dec (x, V1))
        val (V2, gr2) = approxToTypeVar1 (IntSyn.Decl (G, D1), Va2)
      in
        (IntSyn.Pi ((D1, dp), V2), gr1 andalso gr2)
      end
    | approxToTypeVar1W (G, IntSyn.Root (H, S)) =
      (IntSyn.Root (H, 
         case H
           of IntSyn.Const (c) => newSpineVar (G, (IntSyn.constType (c), IntSyn.id))), true)
    | approxToTypeVar1W (G, IntSyn.EVar _) = 
        (IntSyn.newTypeVar (G), false)

  and approxToTypeVar1 (G, Va) = approxToTypeVar1W (G, whnfApprox (Va))

  fun approxToTypeVar (G, Va, r, msg) =
      let
        val (V, gr) = approxToTypeVar1 (G, Va)
      in
        if not gr then ambiguousError (G, V, r, msg) else ();
        V
      end

  fun ensurePi (G, (V, s), (U1, oc1)) =
      (case Whnf.whnf (V, s)
         of (IntSyn.Pi ((IntSyn.Dec (x, V1), P), V2), s) =>
              (V1, V2, s)
          | (V, s) =>
            let
              val V1 = IntSyn.newTypeVar (G)
              val D1 = Names.decLUName (G, IntSyn.Dec (NONE, V1))
              val V2 = IntSyn.newTypeVar (IntSyn.Decl (G, D1))
            in
              unify (G, (V, s), (IntSyn.Pi ((D1, IntSyn.Maybe), V2), IntSyn.id))
              handle Unify.Unify msg => extraneousError (G, (V, s), (U1, oc1));
              (V1, V2, IntSyn.id)
            end)

  (* Given that a term is approximately well-typed, convert it
     to an eta-long, internalized expression (and occurence exp) *)

  fun reconShow (G, Ua) =
      let
        val res as (U, V, oc) = recon (G, Ua)
      in
        showInferred (G, ((U, V), oc));
        res
      end

  and recon (G, TermSyn.Typ (r)) =
        (IntSyn.Uni (IntSyn.Type),
         IntSyn.Uni (IntSyn.Kind),
         Paths.leaf (r))
    | recon (G, TermSyn.Lam (Da1 as TermSyn.Dec (x, _, Va), Ua2, r)) =
      let
        val (D1, oc1Opt) = reconDec (G, Da1, r)
        val (U2, V2, oc2) = reconShow (decl (G, D1), Ua2)
        val r' = Paths.join (r, Paths.toRegion oc2)
      in
        (IntSyn.Lam (D1, U2),
         IntSyn.Pi ((D1, IntSyn.Maybe), V2),
         Paths.bind (r', oc1Opt, oc2))
      end
    | recon (G, TermSyn.Arrow (Ua1, Ua2)) =
      let
        val (V1, L1, oc1) = reconShow (G, Ua1)
        val D1 = IntSyn.Dec (NONE, V1)
        val (V2, L2, oc2) = reconShow (G, Ua2)
        val r' = joinRegions (oc1, oc2)
      in
        (IntSyn.Pi ((D1, IntSyn.No), IntSyn.EClo (V2, IntSyn.shift)),
         L2, Paths.bind (r', SOME (oc1), oc2))
      end
    | recon (G, TermSyn.Pi (Da1, Ua2, r)) =
      let
        val (D1, oc1Opt) = reconDec (G, Da1, r)
        val (V2, L2, oc2) = reconShow (decl (G, D1), Ua2)
        val r' = Paths.join (r, Paths.toRegion oc2)
      in
        (IntSyn.Pi ((D1, IntSyn.Maybe), V2), L2, Paths.bind (r', oc1Opt, oc2))
      end
    | recon (G, TermSyn.Omitobj (Va, r)) =
      let
        val V = approxToTypeVar (G, Va, r, "Ambiguous type for omitted term\n")
        val X = newLoweredEVar (G, (V, IntSyn.id))
      in
        (X, V, Paths.leaf (r))
      end
    | recon (G, TermSyn.Implicit (Va, r)) =
      let
        val V = approxToTypeVar (G, Va, r, "Ambiguous type for implicit argument\n")
        val X = newLoweredEVar (G, (V, IntSyn.id))
      in
        (X, V, Paths.leaf (r))
      end
    | recon (G, TermSyn.Hastype (Ua1, Ua2)) =
      let
        val (U1, V1, oc1) = reconShow (G, Ua1)
        val (V2, L2, oc2) = reconShow (G, Ua2)
      in
        unify (G, (V1, IntSyn.id), (V2, IntSyn.id))
        handle Unify.Unify msg => hasTypeError (G, (V1, oc1), (V2, oc2), msg);
        (U1, V2, oc1)
      end
    | recon (G, TermSyn.Root (hd, sp)) =
      let
        val (H, V, i, r) = reconHead (G, hd)
        val (S, V', os) = reconSpine (G, (V, IntSyn.id), sp)
        val os' = Paths.removeImplicit (i, os)
      in
        (H S, V',
         Paths.root (Paths.toRegionSpine (os', r), Paths.leaf r, i, os'))
      end
    | recon (G, TermSyn.Redex (Ua, sp)) =
      let
        val (U, V, oc) = reconShow (G, Ua)
        val (S, V', os) = reconSpine (G, (V, IntSyn.id), sp)
      in
        (IntSyn.Redex (U, S), V',
         (* mismatch here *)
         Paths.root (Paths.toRegionSpine (os, Paths.toRegion (oc)), oc, 0, os))
      end

  and reconHead (G, TermSyn.Const (H, conDec, r)) =
      let
        val i = IntSyn.conDecImp (conDec)
        val V = IntSyn.conDecType (conDec)
      in
        (case IntSyn.conDecStatus (conDec)
           of IntSyn.Foreign (cs, toForeign) => toForeign
            | _ => fn S => IntSyn.Root (H, S),
         V, i, r)
      end
    | reconHead (G, TermSyn.EVar (name, r)) =
      let
        val s = IntSyn.Shift (IntSyn.ctxLength (G))
        val (U as IntSyn.EVar(_,_,V,_), Va, set) = Names.getEVar name 
        val V' = approxToTypeVar (IntSyn.Null, Va, r, "Ambiguous type for free variable\n")
      in
        case set
          of ref false =>
               (unify (IntSyn.Null, (V, IntSyn.id), (V', IntSyn.id));
                set := true)
           | _ => ();
        (fn S => IntSyn.Redex (IntSyn.EClo (U, s), S),
         IntSyn.EClo (V, s), 0, r)
      end
    | reconHead (G, TermSyn.FVar (name, r)) =
      let
        val s = IntSyn.Shift (IntSyn.ctxLength (G))
        val (V, Va, set) = Names.getFVarType (name)
        val V' = approxToTypeVar (IntSyn.Null, Va, r, "Ambiguous type for free variable\n")
      in
        case set
          of ref false =>
               (unify (IntSyn.Null, (V, IntSyn.id), (V', IntSyn.id));
                set := true)
           | _ => ();
        (fn S => IntSyn.Root (IntSyn.FVar (name, V, s), S),
         IntSyn.EClo (V, s), 0, r)
      end
    | reconHead (G, TermSyn.BVar (k, r)) =
      let
        val (IntSyn.Dec (x, V)) = IntSyn.ctxDec (G, k)
      in
        (fn S => IntSyn.Root (IntSyn.BVar (k), S), V, 0, r)
      end

  and reconSpine (G, (V, s), TermSyn.Nil) =
        (IntSyn.Nil, IntSyn.EClo (V, s), Paths.nils)
    | reconSpine (G, (V, s), TermSyn.App (Ua, sp)) =
      let
        val (U1, V1, oc1) = reconShow (G, Ua)
        val (V1', V2', s') = ensurePi (G, (V, s), (U1, oc1))
        val _ = unify (G, (V1, IntSyn.id), (V1', s'))
            handle Unify.Unify msg => mismatchError (G, (V1', s'), ((U1, V1), oc1), msg)
        val (S, V', os) = reconSpine (G, (V2', Whnf.dotEta (IntSyn.Exp (U1), s')), sp)
      in
        (IntSyn.App (U1, S), V', Paths.app (oc1, os))
      end

  and reconDec (G, TermSyn.Dec (x, UaOpt, Va), r) =
      (case UaOpt
         of SOME (Ua) =>
            let
              val (V, L, oc) = reconShow (G, Ua)
            in
              (IntSyn.Dec (x, V), SOME(oc))
            end
          | _ => (IntSyn.Dec (x, approxToTypeVar (G, Va, r, "Ambiguous omitted type in declaration\n")), NONE))

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
  fun termToApproxExp (Ga, tm) =
      let
        val t = tm (Ga, false)
        val (Ua, Va, r) = approxReconShow (Ga, t)
        (* must check separately -kw *)
        (* val _ = checkType (La, r, "Classifier in declaration is not a type") *)
      in
        t
      end

  fun approxExpToExp (G, t) =
      let
        val (U, V, oc) = reconShow (G, t)
      in
        (U, V)
      end

  (* we should get rid of these in favor of a separate check that the
     resulting expression is at object level -kw *)
  fun termToApproxExp' (Ga, tm) =
      let
	val t = tm (Ga, false)
	val (Ua, Va, r) = approxReconShow (Ga, t)
        val _ = case Ua
                  of NONE => ()
                   | _ => error (r, "Classifier in declaration is not an object")
      in
	t
      end
 
  fun approxExpToExp' (G, t) =
      let
	val (U, V, oc) = reconShow (G, t)
      in
	(U, V)
      end

  (* Converting a declaration to an expression in a context *)
  (* Throws away the associated occurrence tree *)
  fun decToApproxDec (Ga, dec) =
      let
        val Da = dec (Ga, false)
        val rOpt = approxReconDec (Ga, Da)
      in
        Da
      end

  fun approxDecToDec (G, Da, r) =
      let
        val (D, ocOpt) = reconDec (G, Da, r)
      in
        D
      end

  (* termToExp0 (tm) = ((U,V), oc) 
     where . |- U : V
  *)
  fun termToExp0 (tm, qf) =
      let
        val t = tm (IntSyn.Null, qf)
        val (Ua, Va, r) = approxReconShow (IntSyn.Null, t)
        val (U, V, oc) = reconShow (IntSyn.Null, t)
      in
	((U, V), oc)
      end

  fun termToExp (g, tm) =
      let
        val _ = Names.varReset ()

        fun reconCtx1 (IntSyn.Null) = IntSyn.Null
          | reconCtx1 (IntSyn.Decl (g, (d, r))) =
            let
              val Ga = reconCtx1 (g)
            in
              IntSyn.Decl (Ga, decToApproxDec (Ga, d))
            end

        fun reconCtx2 (IntSyn.Null, IntSyn.Null) = IntSyn.Null
          | reconCtx2 (IntSyn.Decl (g, (_, r)), IntSyn.Decl (Ga, Da)) =
            let
              val G = reconCtx2 (g, Ga)
            in
              IntSyn.Decl (G, approxDecToDec (G, Da, r))
            end

        val Ga = reconCtx1 (g)
        val t = termToApproxExp (Ga, tm)
        val G = reconCtx2 (g, Ga)
        val (U, V) = approxExpToExp (G, t)
      in
        (G, U, V)
      end

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
	val _ = resetErrors (fileName)
	val ((V,L), oc) = (Timers.time Timers.recon termToExp0) (tm, true)
	val _ = checkType (L, Paths.toRegion oc, "Query is not a type")
	val Xs = Names.namedEVars ()
	val _ = if freeVar (optName, Xs)
		  then error (Paths.toRegion oc,
			      "Proof term variable " ^ valOf optName
			      ^ " occurs in type")
		else ()
	val _ = checkErrors (Paths.toRegion oc)
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
	val _ = resetErrors (fileName)
	val ((V, L), oc) = (Timers.time Timers.recon termToExp0) (tm, false)
	val level = getUni (L, Paths.toRegion oc, "Classifier in declaration is not a type or kind")
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
	val _ = checkErrors (r)
      in
	(SOME(cd), SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, SOME(tm2)), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset ()
	val _ = resetErrors (fileName)
	val ((V, L), oc2) = (Timers.time Timers.recon termToExp0) (tm2, false)
	val level = getUni (L, Paths.toRegion oc2, "Classifier in definition is not a type or kind")
	val ((U, V'), oc1) = (Timers.time Timers.recon termToExp0) (tm1, false)
	val _ = (Timers.time Timers.recon unify) (IntSyn.Null, (V', IntSyn.id), (V, IntSyn.id))
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
	val _ = checkErrors (r)
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, NONE), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset ()
	val _ = resetErrors (fileName)
	val ((U, V), oc1) = (Timers.time Timers.recon termToExp0) (tm1, false)
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
	val _ = checkErrors (r)
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end

end; (* functor TpRecon *)
