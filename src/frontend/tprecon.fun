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
		 structure Constraints : CONSTRAINTS
		   sharing Constraints.IntSyn = IntSyn'
		 structure TypeCheck : TYPECHECK
		   sharing TypeCheck.IntSyn = IntSyn'
                 structure Conv : CONV
                   sharing Conv.IntSyn = IntSyn'
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
    | Lam of Dec * Term
    | Arrow of Term * Term
    | Pi of Dec * Term
    | Omitobj of IntSyn.Exp * Paths.region
    | Implicit of IntSyn.Exp * Paths.region
    | Hastype of Term * Term
    | Root of Head * Spine
    | Redex of Term * Spine

    and Head =
      EVar of string * int * Paths.region
    | FVar of string * Paths.region
    | BVar of int * Paths.region
    | Const of IntSyn.Head * IntSyn.ConDec * Paths.region

    and Spine =
      Nil
    | App of Term * Spine

    and Dec = Dec of name option * Term option * IntSyn.Exp * Paths.region

  end

  type term = IntSyn.dctx * int option -> TermSyn.Term
  type dec = IntSyn.dctx * int option -> TermSyn.Dec

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
	    | findBVar' (IntSyn.Decl (Ga', IntSyn.Dec (NONE, _)), k) = findBVar' (Ga', k+1)
            | findBVar' (IntSyn.Decl (Ga', IntSyn.Dec (SOME(name'), _)), k) =
	      if name = name' then SOME(k)
	      else findBVar' (Ga', k+1)
      in
	findBVar' (Ga, 1)
      end

  (* findConst (name)
      = SOME (c, i, V) where  c : V and c has i implicit arguments, c is called name
      = NONE  if so such c exists.
  *)
  fun findConst (qid) =
      (case Names.constLookup qid
         of NONE => (case Option.mapPartial CSManager.parse (Names.unqualified qid)
                       of NONE => NONE
                        | SOME (cs, conDec) => SOME (IntSyn.FgnConst (cs, conDec), conDec))
          | SOME(cid) => (case IntSyn.sgnLookup(cid)
			    of (conDec as IntSyn.ConDec _) => SOME (IntSyn.Const(cid), conDec)
			     | (conDec as IntSyn.ConDef _) => SOME (IntSyn.Def(cid), conDec)
                             | (conDec as IntSyn.AbbrevDef _) => SOME (IntSyn.NSDef(cid), conDec)))

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

  fun inc NONE = NONE
    | inc (SOME depth) = SOME (depth+1)

  (* Free variable *)
  (* Translated to FVar in declarations, to EVar in queries *)
  fun var (name, r, SOME depth) =
      let
        val _ = Names.getEVar name (* get the variable into the Names
                                      table before we do any printing *)
      in
        TermSyn.Root (TermSyn.EVar (name, depth, r), TermSyn.Nil)
      end
    | var (name, r, NONE) =
      let
        val _ = Names.getFVarType name (* get the variable into the Names
                                          table before we do any printing *)
      in
        TermSyn.Root (TermSyn.FVar (name, r), TermSyn.Nil)
      end

  fun undeclError (qid, r, depth) =
      (error (r, "Undeclared identifier " ^
              Names.qidToString (valOf (Names.constUndef qid)));
       (* translate to FVar or EVar *)
       var (Names.qidToString qid, r, depth))

  (* The remaining functions appear in the interface *)

  (* Resolving lower-case, upper-case or quoted identifiers *)
  (* lcid -- lower case identifier *)
  fun lcid (ids, name, r) (Ga, depth) =
      let
        val qid = Names.Qid (ids, name)
      in
        case Option.mapPartial (fn name => findBVar (name, Ga))
                               (Names.unqualified qid)
          of NONE => (case findConst (qid)
                        of NONE => undeclError (qid, r, depth)
                         | SOME info => (const (info, r)))
           | SOME n => bvar (n, r)
      end

  (* ucid -- upper case identifier *)
  fun ucid (ids, name, r) (Ga, depth) =
      let
        val qid = Names.Qid (ids, name)
      in
        case Option.mapPartial (fn name => findBVar (name, Ga))
                               (Names.unqualified qid)
          of NONE => (case findConst (qid)
                        of NONE => (case Names.unqualified qid
                                      of SOME name => var (name, r, depth)
                                       | NONE => undeclError (qid, r, depth))
                         | SOME info => const (info, r))
           | SOME n => bvar (n, r)
      end

  (* quid -- quoted identifier *)
  (* currently not used *)
  fun quid (ids, name, r) (Ga, depth) =
      let
        val qid = Names.Qid (ids, name)
      in
        case findConst (qid)
          of NONE => undeclError (qid, r, depth)
           | SOME info => const (info, r)
      end

  (* scon -- string constants *)
  fun scon (name, r) (Ga, depth) =
      (case CSManager.parse name
         of NONE => (error (r, "Strings unsupported in current signature");
                     var (name, r, depth))
          | SOME (cs, conDec) => const ((IntSyn.FgnConst (cs, conDec), conDec), r))

  fun spineAppend (TermSyn.Nil, Ua) =
        TermSyn.App (Ua, TermSyn.Nil)
    | spineAppend (TermSyn.App (Ua1, Ua2), Ua3) =
        TermSyn.App (Ua1, spineAppend (Ua2, Ua3))

  (* Application "tm1 tm2" *)
  fun app (tm1, tm2) (Ga, depth) =
      (case tm1 (Ga, depth)
         of TermSyn.Root (hd, sp) =>
              TermSyn.Root (hd, spineAppend (sp, tm2 (Ga, depth)))
          | TermSyn.Redex (tm, sp) =>
              TermSyn.Redex (tm, spineAppend (sp, tm2 (Ga, depth)))
          | tm1 => TermSyn.Redex (tm1, TermSyn.App (tm2 (Ga, depth), TermSyn.Nil)))

  (* Non-dependent function type "tm1 -> tm2" *)
  fun arrow (tm1, tm2) (Ga, depth) = TermSyn.Arrow (tm1 (Ga, depth), tm2 (Ga, depth))

  (* Non-dependent function type "tm2 <- tm1" *)
  fun backarrow (tm2, tm1) (Ga, depth) = arrow (tm1, tm2) (Ga, depth)

  (* Explicit type ascription "tm1 : tm2" *)
  fun hastype (tm1, tm2) (Ga, depth) = TermSyn.Hastype (tm1 (Ga, depth), tm2 (Ga, depth))

  (* Omitted objects (from underscore) "_" *)
  fun omitobj (r) (Ga, depth) = TermSyn.Omitobj (IntSyn.newTypeVar (IntSyn.Null), r)

  (* Dependent function type "{id:tm} tm" where dec = "id:tm" *)
  fun pi (d, tm) (Ga, depth) =
      let
        val dec as TermSyn.Dec (x, _, Va, _) = d (Ga, depth)
        val Da = IntSyn.Dec (x, Va)
      in
        TermSyn.Pi (dec, tm (IntSyn.Decl (Ga, Da), inc depth))
      end

  (* Lambda abstraction "[id:tm] tm" where dec = "id:tm" *)
  fun lam (d, tm) (Ga, depth) =
      let
        val dec as TermSyn.Dec (x, _, Va, _) = d (Ga, depth)
        val Da = IntSyn.Dec (x, Va)
      in
        TermSyn.Lam (dec, tm (IntSyn.Decl (Ga, Da), inc depth))
      end

  (* Type "type" *)
  fun typ (r) (Ga, depth) = TermSyn.Typ (r)

  (* Declarations "id:tm" *)
  fun dec (x, tm, r) (Ga, depth) =
        TermSyn.Dec (x, SOME (tm (Ga, depth)), IntSyn.newTypeVar (IntSyn.Null), r)

  (* Declarations with implicit type "id" *)
  fun dec0 (x, r) (Ga, depth) =
        TermSyn.Dec (x, NONE, IntSyn.newTypeVar (IntSyn.Null), r)

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

  fun mismatchError (G, (V1', s), ((U2, V2), r), msg) =
      let
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

  fun instError (G, U1, (U2, r), msg) =
      let
        val U1fmt = formatExp (G, U1)
        val U2fmt = formatExp (G, U2)
        val diff = F.Vbox0 0 1
                   [F.String "Existing:    ", F.Space, U1fmt, F.Break,
                    F.String "Instantiator:", F.Space, U2fmt]
      in
        error (r, "Inconsistent instantiation\n"
               ^ F.makestring_fmt diff ^ "\n" ^ msg)
      end

  fun closedError (G, (U, r)) =
      let
        val Ufmt = formatExp (G, U)
        val nonClosed = F.HVbox [F.String "Instantiator:", F.Space, Ufmt, F.Break,
                                 F.String "contains free variables after term reconstruction"]
      in
        error (r, "Ambiguous instantiation\n"
               ^ F.makestring_fmt nonClosed)
      end

  fun checkHasTypeUnis ((level1, r1), (level2, r2), msg) =
      (case (level1, level2)
         of (IntSyn.Type, IntSyn.Type) => ()
          | (IntSyn.Type, IntSyn.Kind) =>
              error (Paths.join (r1, r2), msg ^ "\nSubject is an object, classifier is kind")
          | (IntSyn.Kind, IntSyn.Type) =>
              error (Paths.join (r1, r2), msg ^ "\nSubject is type family, classifier is type")
          | (IntSyn.Kind, IntSyn.Kind) => ())

  fun checkInstUnis (level1, (level2, r2), msg) =
      (case (level1, level2)
         of (IntSyn.Type, IntSyn.Type) => ()
          | (IntSyn.Type, IntSyn.Kind) =>
              error (r2, msg ^ "\nExisting constant is an object, instantiator is a type family")
          | (IntSyn.Kind, IntSyn.Type) =>
              error (r2, msg ^ "\nExisting constant is a type family, instantiator is a type")
          | (IntSyn.Kind, IntSyn.Kind) => ())

  fun hasTypeError (G, (V1, oc1), (V2, oc2), msg1, msg2) =
      let
	val r2 = Paths.toRegion oc2
	val V1fmt = formatExp (G, V1)
	val V2fmt = formatExp (G, V2)
	val diff = F.Vbox0 0 1
	           [F.String "Synthesized: ", V1fmt, F.Break,
		    F.String "Ascribed:    ", V2fmt]
      in
	error (r2, msg1 ^ "\n"
	           ^ F.makestring_fmt diff ^ "\n"
	           ^ msg2)
      end

  fun extraneousError (G, (V1, s), (U2, oc2)) =
      let
	val V1fmt = formatExp (G, IntSyn.EClo (V1, s))
	val nonFun = F.HVbox [F.String "Reconstructed:", F.Space, V1fmt, F.Break,
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
        error (r, msg ^ "\n" ^ F.makestring_fmt amb)
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

  (* If Ga |~ Ua : Va
     then if Ga |~ Va : L for some L, returns L
     otherwise Ua = type, Va = kind, and error is flagged *)
  fun inferUni (Va, r, msg) =
      (case whnfApprox (Va)
         of (IntSyn.Uni (IntSyn.Kind)) => (error (r, msg); IntSyn.Kind)
          | (IntSyn.Uni (IntSyn.Type)) => IntSyn.Kind
          | (IntSyn.Pi (_, Va')) => inferUni (Va', r, msg)
          | _ => IntSyn.Type)

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

  and makeApproxCtx (IntSyn.Null) = IntSyn.Null
    | makeApproxCtx (IntSyn.Decl (G, D)) =
        IntSyn.Decl (makeApproxCtx G, makeApproxDec D)

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
    | approxRecon (Ga, TermSyn.Lam (d1 as TermSyn.Dec (x, _, Va1, r), t2)) =
      let
        val Da1 = approxReconDec (Ga, d1)
        val (Ua2Opt, Va2, r2) = approxReconShow (IntSyn.Decl (Ga, Da1), t2)
        val _ = case Ua2Opt
                  of NONE => ()
                   | SOME _ => error (r2, "Abstraction body cannot be a type family or kind")
      in
        (NONE, IntSyn.Pi ((IntSyn.Dec (x, Va1), IntSyn.Maybe), Va2),
         Paths.join (r, r2))
      end
    | approxRecon (Ga, TermSyn.Arrow (t1, t2)) =
      let
        val (Va1Opt, La1, r1) = approxReconShow (Ga, t1)
        val _ = checkType (La1, r1, "Domain of function is not a type")
        val (Va2Opt, La2, r2) = approxReconShow (Ga, t2)
        val _ = checkUni (La2, r2, "Range of function is not a type or kind")
        val Va1 = (case Va1Opt
                     of NONE => IntSyn.newTypeVar (IntSyn.Null)
                      | SOME Va1 => Va1)
        val Va2 = (case Va2Opt
                     of NONE => IntSyn.newTypeVar (IntSyn.Null)
                      | SOME Va2 => Va2)
      in
        (SOME (IntSyn.Pi ((IntSyn.Dec (NONE, Va1), IntSyn.No), Va2)),
         La2, Paths.join (r1, r2))
      end
    | approxRecon (Ga, TermSyn.Pi (d1 as TermSyn.Dec (x, _, Va1, r), t2)) =
      let
        val Da1 = approxReconDec (Ga, d1)
        val (Va2Opt, La2, r2) = approxReconShow (IntSyn.Decl (Ga, Da1), t2)
        val _ = checkUni (La2, r2, "Range of function is not a type or kind")
        val Va2 = (case Va2Opt
                     of NONE => IntSyn.newTypeVar (IntSyn.Null)
                      | SOME Va2 => Va2)
      in
        (SOME (IntSyn.Pi ((IntSyn.Dec (x, Va1), IntSyn.Maybe), Va2)),
         La2, Paths.join (r, r2))
      end
    | approxRecon (Ga, TermSyn.Omitobj (Va, r)) =
        (NONE, Va, r)
    | approxRecon (Ga, TermSyn.Implicit (Va, r)) =
        (NONE, Va, r)
    | approxRecon (Ga, TermSyn.Hastype (t1, t2)) =
      let
        val (Va2Opt, La2, r2) = approxReconShow (Ga, t2)
        val level2 = getUni (La2, r2, "Classifier in ascription is not a type or kind")
        val (Ua1Opt, Va1, r1) = approxReconShow (Ga, t1)
        val level1 = inferUni (Va1, r1, "Subject of ascription cannot be a kind")
        val _ = checkHasTypeUnis ((level1, r1), (level2, r2),
                                  "Level mismatch in ascription")
        val Va2 = (case Va2Opt
                     of NONE => IntSyn.newTypeVar (IntSyn.Null)
                      | SOME Va2 => Va2)
      in
        shape (Va1, Va2)
        handle Unify.Unify msg => ();
        (* use ascribed type if unification failed *)
        (Ua1Opt, Va2, r1)
      end
    | approxRecon (Ga, TermSyn.Root (hd, sp)) =
      let
        val (UaOpt, Va, r) = approxReconHead (Ga, hd)
        val (Va', r') = approxReconSpine (Ga, Va, r, sp)
      in
        (UaOpt, Va', r')
      end
    | approxRecon (Ga, TermSyn.Redex (t, sp)) =
      let
        val (UaOpt, Va, r) = approxReconShow (Ga, t)
        val (Va', r') = approxReconSpine (Ga, Va, r, sp)
      in
        (UaOpt, Va', r')
      end

  and approxReconHead (Ga, TermSyn.EVar (name, depth, r)) =
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
        val (IntSyn.Dec (_, Va)) = IntSyn.ctxLookup (Ga, n)
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
        val (Ua1Opt, Va1, r1) = approxReconShow (Ga, t)
        val _ = case Ua1Opt
                  of NONE => ()
                   | _ => error (r1, "Argument to function cannot be a type family or kind")
        val (Va1', Va2') = ensurePiApprox (Va)
      in
        shape (Va1, Va1')
        handle Unify.Unify msg => ();
        approxReconSpine (Ga, Va2', Paths.join (r, r1), sp)
      end

  and approxReconDec (Ga, TermSyn.Dec (name, tOpt, Va1, r)) =
      (case tOpt
         of SOME t =>
            let
              val (VaOpt, La, r1) = approxReconShow (Ga, t)
              val _ = checkType (La, r1, "Classifier in declaration is not a type")
              val Va = (case VaOpt
                          of NONE => IntSyn.newTypeVar (IntSyn.Null)
                           | SOME Va => Va)
            in
              (* should never fail *)
              shape (Va, Va1)
              handle Unify.Unify msg => ();
              IntSyn.Dec (name, Va1)
            end
          | NONE => IntSyn.Dec (name, Va1))

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
    | recon (G, TermSyn.Lam (Da1 as TermSyn.Dec (x, _, Va, r), Ua2)) =
      let
        val (D1, oc1Opt) = reconDec (G, Da1)
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
    | recon (G, TermSyn.Pi (Da1 as TermSyn.Dec (_, _, _, r), Ua2)) =
      let
        val (D1, oc1Opt) = reconDec (G, Da1)
        val (V2, L2, oc2) = reconShow (decl (G, D1), Ua2)
        val r' = Paths.join (r, Paths.toRegion oc2)
      in
        (IntSyn.Pi ((D1, IntSyn.Maybe), V2), L2, Paths.bind (r', oc1Opt, oc2))
      end
    | recon (G, TermSyn.Omitobj (Va, r)) =
      let
        val V = approxToTypeVar (G, Va, r, "Ambiguous type for omitted term")
        val X = newLoweredEVar (G, (V, IntSyn.id))
      in
        (X, V, Paths.leaf (r))
      end
    | recon (G, TermSyn.Implicit (Va, r)) =
      let
        val V = approxToTypeVar (G, Va, r, "Ambiguous type for implicit argument")
        val X = newLoweredEVar (G, (V, IntSyn.id))
      in
        (X, V, Paths.leaf (r))
      end
    | recon (G, TermSyn.Hastype (Ua1, Ua2)) =
      let
        val (V2, L2, oc2) = reconShow (G, Ua2)
        val (U1, V1, oc1) = reconShow (G, Ua1)
      in
        unify (G, (V1, IntSyn.id), (V2, IntSyn.id))
        handle Unify.Unify msg => hasTypeError (G, (V1, oc1), (V2, oc2),
                                                "Type mismatch in ascription", msg);
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
    | reconHead (G, TermSyn.EVar (name, depth, r)) =
      let
        fun ctxDrop (G, 0) = G
          | ctxDrop (IntSyn.Decl (G, _), i) = ctxDrop (G, i-1)
        val G' = ctxDrop (G, depth)
        val s = IntSyn.Shift depth
        val (U as IntSyn.EVar(_,_,V,_), Va, set) = Names.getEVar name 
        val V' = approxToTypeVar (G', Va, r, "Ambiguous type for free variable")
      in
        case set
          of ref false =>
               (unify (G', (V, IntSyn.id), (V', IntSyn.id));
                set := true)
           | _ => ();
        (fn S => IntSyn.Redex (IntSyn.EClo (U, s), S),
         IntSyn.EClo (V, s), 0, r)
      end
    | reconHead (G, TermSyn.FVar (name, r)) =
      let
        val s = IntSyn.Shift (IntSyn.ctxLength (G))
        val (V, Va, set) = Names.getFVarType (name)
        val V' = approxToTypeVar (IntSyn.Null, Va, r, "Ambiguous type for free variable")
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
            handle Unify.Unify msg => mismatchError (G, (V1', s'), ((U1, V1), Paths.toRegion oc1), msg)
        val (S, V', os) = reconSpine (G, (V2', Whnf.dotEta (IntSyn.Exp (U1), s')), sp)
      in
        (IntSyn.App (U1, S), V', Paths.app (oc1, os))
      end

  and reconDec (G, TermSyn.Dec (x, UaOpt, Va, r)) =
      (case UaOpt
         of SOME (Ua) =>
            let
              val (V, L, oc) = reconShow (G, Ua)
            in
              (IntSyn.Dec (x, V), SOME(oc))
            end
          | _ => (IntSyn.Dec (x, approxToTypeVar (G, Va, r, "Ambiguous omitted type in declaration")), NONE))

  (* Constant declarations *)
  datatype condec =
      condec of name * term
    | condef of name option * term * term option
    | blockdec of name * dec list * dec list

  (* Queries, with optional proof term variable *)
  datatype query =
      query of name option * term

  type rdec = IntSyn.Dec * Paths.occExp option * Paths.region

  fun approxReconCtx (Ga, IntSyn.Null, depth) = (Ga, IntSyn.Null)
    | approxReconCtx (Ga, IntSyn.Decl (g, d), depth) =
      let
        val (Ga', decs) = approxReconCtx (Ga, g, depth)
        val dec = d (Ga', depth)
        val Da = approxReconDec (Ga', dec)
      in
        (IntSyn.Decl (Ga', Da), IntSyn.Decl (decs, dec))
      end

  fun approxReconCtxs (Ga, nil, depth) = nil
    | approxReconCtxs (Ga, g::gs, depth) =
      let
        val (Ga', decs) = approxReconCtx (Ga, g, depth)
      in
        decs::approxReconCtxs (Ga', gs, depth)
      end

  fun reconCtx (G, IntSyn.Null) = (G, IntSyn.Null)
    | reconCtx (G, IntSyn.Decl (Ga, dec as TermSyn.Dec (_, _, _, r))) =
      let
        val (G1, G2) = reconCtx (G, Ga)
        val (D, ocOpt) = reconDec (G1, dec)
      in
        (IntSyn.Decl (G1, D), IntSyn.Decl (G2, (D, ocOpt, r)))
      end

  fun reconCtxs (G, nil) = nil
    | reconCtxs (G, Ga::Gas) =
      let
        val (G1, G2) = reconCtx (G, Ga)
      in
        G2::reconCtxs (G1, Gas)
      end

  fun ctxToCtx g =
      let
        val _ = Names.varReset IntSyn.Null
        val (_, decs) = approxReconCtx (IntSyn.Null, g, NONE)
        val (_, G) = reconCtx (IntSyn.Null, decs)
      in
        G
      end      

  fun ctxsToCtxs gs =
      let
        val _ = Names.varReset IntSyn.Null
        val decsList = approxReconCtxs (IntSyn.Null, gs, NONE)
        val Gs = reconCtxs (IntSyn.Null, decsList)
      in
        Gs
      end

  fun termToExp (g, tm) =
      let
        val _ = Names.varReset IntSyn.Null
        val (Ga, decs) = approxReconCtx (IntSyn.Null, g, NONE)
        val t = tm (Ga, NONE)
        val (UaOpt, Va, r) = approxRecon (Ga, t)
        val (G1, G2) = reconCtx (IntSyn.Null, decs)
        val (U, V, oc) = recon (G1, t)
      in
        (G2, U, V, oc)
      end

  (* termToQuery0 (tm) = (V, oc) 
     where . |- V : type
  *)
  fun termToQuery0 (tm) =
      let
        val t = tm (IntSyn.Null, SOME 0)
        val (VaOpt, La, r) = approxReconShow (IntSyn.Null, t)
        val _ = checkType (La, r, "Query is not a type")
        val (V, L, oc) = reconShow (IntSyn.Null, t)
      in
	(V, oc)
      end

  (* termToDec0 (tm) = ((V, level), oc) 
     where . |- V : Uni level
  *)
  fun termToDec0 (tm) =
      let
        val t = tm (IntSyn.Null, NONE)
        val (VaOpt, La, r) = approxReconShow (IntSyn.Null, t)
        val level = getUni (La, r, "Classifier in declaration is not a type or kind")
        val (V, L, oc) = reconShow (IntSyn.Null, t)
      in
	((V, level), oc)
      end

  (* termToDef0 (tm1, tm2Opt) = ((U, V, level), (oc1, oc2Opt))
     where . |- U : V
           . |- V : Uni level
  *)
  fun termToDef0 (tm1, SOME tm2) =
      let
        val t2 = tm2 (IntSyn.Null, NONE)
        val t1 = tm1 (IntSyn.Null, NONE)
        val (Va2Opt, La2, r2) = approxReconShow (IntSyn.Null, t2)
        val level2 = getUni (La2, r2, "Classifier in definition is not a type or kind")
        val (Ua1Opt, Va1, r1) = approxReconShow (IntSyn.Null, t1)
        val level1 = inferUni (Va1, r1, "Kinds cannot be defined")
        val _ = checkHasTypeUnis ((level1, r1), (level2, r2),
                                  "Level mismatch in definition")
        val Va2 = (case Va2Opt
                     of NONE => IntSyn.newTypeVar (IntSyn.Null)
                      | SOME Va2 => Va2)
        val _ = shape (Va1, Va2)
                handle Unify.Unify msg => ()
        val (V2, L2, oc2) = reconShow (IntSyn.Null, t2)
        val (U1, V1, oc1) = reconShow (IntSyn.Null, t1)
      in
        unify (IntSyn.Null, (V1, IntSyn.id), (V2, IntSyn.id))
        handle Unify.Unify msg => hasTypeError (IntSyn.Null, (V1, oc1), (V2, oc2),
                                                "Type mismatch in definition", msg);
        ((U1, V2, level1), (oc1, SOME oc2))
      end
    | termToDef0 (tm1, NONE) =
      let
        val t1 = tm1 (IntSyn.Null, NONE)
        val (Ua1Opt, Va1, r1) = approxReconShow (IntSyn.Null, t1)
        val level1 = inferUni (Va1, r1, "Kinds cannot be defined")
        val (U1, V1, oc1) = reconShow (IntSyn.Null, t1)
      in
        ((U1, V1, level1), (oc1, NONE))
      end

  (* freeVar (XOpt, [(X1,"X1"),...,(Xn,"Xn")]) = true
     iff XOpt = SOME("Xi"), false otherwise
  *)
  fun freeVar (SOME(name), Xs) =
        List.exists (fn (_, name') => name = name') Xs
    | freeVar _ = false

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
	val _ = Names.varReset IntSyn.Null
	val _ = resetErrors fileName
	val (V, oc) = (Timers.time Timers.recon termToQuery0) (tm)
	val Xs = Names.namedEVars ()
	val _ = if freeVar (optName, Xs)
		  then error (Paths.toRegion oc,
			      "Proof term variable " ^ valOf optName
			      ^ " occurs in type")
		else ()
	val _ = checkErrors ()
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
	val _ = Names.varReset IntSyn.Null
	val _ = resetErrors fileName
	val ((V, level), oc) = (Timers.time Timers.recon termToDec0) (tm)
        val (i, V') = (Timers.time Timers.abstract Abstract.abstractDecImp) V
	                handle Abstract.Error (msg)
			       => raise Abstract.Error (Paths.wrap (r, msg))
	val cd = Names.nameConDec (IntSyn.ConDec (name, NONE, i, IntSyn.Normal, V', level))
	val ocd = Paths.dec (i, oc)
	val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni (level)) 
		else ()
	val _ = checkErrors ()
      in
	(SOME(cd), SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, SOME(tm2)), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset IntSyn.Null
	val _ = resetErrors fileName
        val ((U, V, level), (oc1, SOME oc2)) =
              (Timers.time Timers.recon termToDef0) (tm1, SOME tm2)
	val (i, (U'', V'')) =
	        (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
		handle Abstract.Error (msg)
		          => raise Abstract.Error (Paths.wrap (r, msg))
	val name = case optName of NONE => "_" | SOME(name) => name
	val ocd = Paths.def (i, oc1, SOME(oc2))
        val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, NONE, i, U'', V'', level))
		 else (case level
			 of IntSyn.Kind => error (r, "Type families cannot be defined, only objects")
		          | _ => ();
		       Strict.check ((U'', V''), SOME(ocd));
		       Names.nameConDec (IntSyn.ConDef (name, NONE, i, U'', V'', level)))
		    
       val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni (level));
			(Timers.time Timers.checking TypeCheck.check) (U'', V''))
		else ()
	val _ = checkErrors ()
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, NONE), Paths.Loc (fileName, r), abbFlag) =
      let
	val _ = Names.varReset IntSyn.Null
	val _ = resetErrors fileName
        val ((U, V, level), (oc1, NONE)) =
              (Timers.time Timers.recon termToDef0) (tm1, NONE)
	val (i, (U'', V'')) =
	        (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
		handle Abstract.Error (msg)
		          => raise Abstract.Error (Paths.wrap (r, msg))
	val name = case optName of NONE => "_" | SOME(name) => name
	val ocd = Paths.def (i, oc1, NONE)
        val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, NONE, i, U'', V'', level))
		 else (case level
			 of IntSyn.Kind => error (r, "Type families cannot be defined, only objects")
		          | _ => ();
		       Strict.check ((U'', V''), SOME(ocd));
		       Names.nameConDec (IntSyn.ConDef (name, NONE, i, U'', V'', level)))
	           
        val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
		else ()
	val _ = if !Global.doubleCheck
		  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni (level));
			(Timers.time Timers.checking TypeCheck.check) (U'', V''))
		else ()
	val _ = checkErrors ()
	val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
	(optConDec, SOME(ocd))
      end
    | condecToConDec (blockdec (name, Lsome, Lblock), Paths.Loc (fileName, r), abbFlag) =
      let
	fun makectx nil = IntSyn.Null
	  | makectx (D :: L) = IntSyn.Decl (makectx L, D)
	fun ctxToList (IntSyn.Null, acc) = acc
	  | ctxToList (IntSyn.Decl (G, D), acc) = ctxToList (G, D :: acc)
	fun join (NONE, r) = SOME(r)
	  | join (SOME(r1), r2) = SOME (Paths.join (r1, r2))
	fun ctxRegion (IntSyn.Null) = (IntSyn.Null, NONE)
	  | ctxRegion (IntSyn.Decl (G, (D, ocOpt, r))) =
  	    let
	      val (G', rOpt) = ctxRegion G
	    in
	      (IntSyn.Decl (G', D), join (rOpt, r))
	    end
	fun ctxAppend (G, IntSyn.Null) = G
	  | ctxAppend (G, IntSyn.Decl (G', D)) = IntSyn.Decl (ctxAppend (G, G'), D)
	fun ctxBlockToString (G0, (G1, G2)) =
  	    let
	      val _ = Names.varReset IntSyn.Null
	      val G0' = Names.ctxName G0
	      val G1' = Names.ctxLUName G1
	      val G2' = Names.ctxLUName G2
	    in
	      Print.ctxToString (IntSyn.Null, G0') ^ "\n"
	      ^ (case G1' of IntSyn.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
	      ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
	    end
	fun checkFreevars (IntSyn.Null, (G1, G2), r) = ()
	  | checkFreevars (G0, (G1, G2), r) =
  	    let
	      val _ = Names.varReset IntSyn.Null
	      val G0' = Names.ctxName G0
	      val G1' = Names.ctxLUName G1
	      val G2' = Names.ctxLUName G2
	    in
	      error (r, "Free variables in context block after term reconstruction:\n"
		     ^ ctxBlockToString (G0', (G1', G2')))
	    end

	val [Gsome, Gblock] = (Timers.time Timers.recon ctxsToCtxs) [(makectx Lsome), (makectx Lblock)]
	val (Gsome', r1Opt) = ctxRegion Gsome
	val (Gblock', SOME(r2)) = ctxRegion Gblock	(* Gblock cannot be empty *)
	val SOME(r) = join (r1Opt, r2)
	val (G0, [Gsome'', Gblock'']) =	(* closed nf *)
	  Abstract.abstractCtxs [Gsome', Gblock'] 
	  handle Constraints.Error (C)
	  => (raise Error (Paths.wrap (r, "Constraints remain in context block after term reconstruction:\n"
		    ^ ctxBlockToString (IntSyn.Null, (Gsome', Gblock')) ^ "\n"
		    ^ Print.cnstrsToString C)))
	val _ = checkFreevars (G0, (Gsome'', Gblock''), r)
	val bd = IntSyn.BlockDec (name, NONE, Gsome'', ctxToList (Gblock'', nil))
        val _ = if !Global.chatter >= 3
		  then print ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
		else ()

      in
	(SOME bd, NONE)
      end

  fun lowerRigid (0, G, V, sc) =
        (G, sc IntSyn.Nil, V)
    | lowerRigid (i, G, IntSyn.Pi ((D, _), V), sc) =
        lowerRigid (i-1, IntSyn.Decl (G, D), V,
                    fn S => sc (IntSyn.App (IntSyn.Root (IntSyn.BVar i, IntSyn.Nil), S)))

  fun lowerFlex (0, G, (V, s), sc) =
        (sc IntSyn.Nil, IntSyn.EClo (V, s))
    | lowerFlex (i, G, (IntSyn.Pi ((D as IntSyn.Dec (_, V1), _), V2), s), sc) =
      let
        val X = IntSyn.newEVar (G, IntSyn.EClo (V1, s))
      in
        lowerFlex (i-1, G,
                   (V2, IntSyn.Dot (IntSyn.Exp X, s)),
                   fn S => sc (IntSyn.App (X, S)))
      end

  fun getDecInfo dec =
      let
        val (name, parent, i, UOpt, V, level) =
            (case dec
               of IntSyn.ConDec (name, parent, i, _, V, level) =>
                    (name, parent, i, NONE, V, level)
                | IntSyn.SkoDec (name, parent, i, V, level) =>
                    (name, parent, i, NONE, V, level)
                | IntSyn.ConDef (name, parent, i, U, V, level) =>
                    (name, parent, i, SOME U, V, level)
                | IntSyn.AbbrevDef (name, parent, i, U, V, level) => 
                    (name, parent, i, SOME U, V, level))
      in
        (name, parent, i, UOpt, V, level)
      end

  fun internalInst (condec1, condec2, r) =
      let
        val (name, parent, i1, U1Opt, V1, level1) = getDecInfo condec1
        val IntSyn.AbbrevDef (_, _, i2, U2, V2, level2) = condec2
        val _ = checkInstUnis (level1, (level2, r),
                               "Level mismatch in instantiation")

        (* This may be rather useless since it doesn't even allow
           permuting the implicit arguments.  Unification
           with parameter variables would allow this while still
           avoiding the generation of undesirable constraints. -kw *)
        val simple = i1 = i2
              andalso Conv.conv ((V1, IntSyn.id), (V2, IntSyn.id))
              andalso (case U1Opt
                         of NONE => true
                          | SOME U1 => Conv.conv ((U1, IntSyn.id), (U2, IntSyn.id)))
      in
        if simple
          then IntSyn.AbbrevDef (name, parent, i2, U2, V2, level2)
        else let
          val _ = Names.varReset IntSyn.Null

          fun sc S = case U1Opt
                       of NONE => NONE
                        | SOME U1 => SOME (IntSyn.Redex (U1, S))
          val (G, Ul1Opt, Vl1) = lowerRigid (i1, IntSyn.Null, V1, sc)

          val s = IntSyn.Shift i1 (* |G| = i1 *)
          val (Ul2, Vl2) = lowerFlex (i2, G, (V2, s),
                                      fn S => IntSyn.Redex (U2, S))

          val _ = unify (G, (Vl1, IntSyn.id), (Vl2, IntSyn.id))
                  handle Unify.Unify msg =>
                    mismatchError (G, (Vl1, IntSyn.id), ((Ul2, Vl2), r), msg);
          val _ = (case Ul1Opt
                     of NONE => ()
                      | SOME Ul1 =>
                          unify (G, (Ul1, IntSyn.id), (Ul2, IntSyn.id))
                          handle Unify.Unify msg =>
                            instError (G, Ul1, (Ul2, r), msg));

          val _ = if Abstract.closedExp (G, (Ul2, IntSyn.id)) then ()
                  else closedError (G, (Ul2, r))
          val U2 = Whnf.normalize (Abstract.raiseTerm (G, Ul2), IntSyn.id)
          val V2 = Whnf.normalize (Abstract.raiseType (G, Vl2), IntSyn.id)
          val _ = if !Global.doubleCheck
                    then ((Timers.time Timers.checking TypeCheck.check) (V2, IntSyn.Uni level2);
                          (Timers.time Timers.checking TypeCheck.check) (U2, V2);
                          (Timers.time Timers.checking TypeCheck.checkConv) (V1, V2);
                          case U1Opt
                            of NONE => ()
                             | SOME U1 => 
                          (Timers.time Timers.checking TypeCheck.checkConv) (U1, U2))
                  else ()
        in
          IntSyn.AbbrevDef (name, parent, i1, U2, V2, level2)
        end
      end

  fun externalInst (dec, tm, r) =
      let
        val (name, parent, i1, U1Opt, V1, level1) = getDecInfo dec

        fun sc S = case U1Opt
                     of NONE => NONE
                      | SOME U1 => SOME (IntSyn.Redex (U1, S))
        val (G, Ul1Opt, Vl1) = lowerRigid (i1, IntSyn.Null, V1, sc)

        val Ga = makeApproxCtx G
        val _ = Names.varReset G
        val t2 = tm (Ga, SOME 0)
        val (Ua2Opt, Va2, r2) = approxReconShow (Ga, t2)
        val level2 = inferUni (Va2, r2, "Instantiating term cannot be a kind")
        val _ = checkInstUnis (level1, (level2, r2),
                               "Level mismatch in instantiation")
        val (Va1, _) = makeApprox Vl1
        val _ = shape (Va1, Va2)
                handle Unify.Unify msg => ()
        val _ = (case (Ul1Opt, Ua2Opt)
                   of (SOME Ul1, SOME Ua2) =>
                      let
                        val (Ua1, _) = makeApprox Ul1
                      in
                        shape (Ua1, Ua2)
                        handle Unify.Unify msg => ()
                      end
                    | _ => ())
        val (Ul2, Vl2, oc2) = reconShow (G, t2)
        val _ = unify (G, (Vl1, IntSyn.id), (Vl2, IntSyn.id))
                handle Unify.Unify msg =>
                  mismatchError (G, (Vl1, IntSyn.id), ((Ul2, Vl2), r2),
                                 msg)
        val _ = case Ul1Opt
                  of NONE => ()
                   | SOME Ul1 => unify (G, (Ul1, IntSyn.id), (Ul2, IntSyn.id))
                handle Unify.Unify msg =>
                  instError (G, Ul1, (Ul2, r2),
                             msg)

        val _ = if Abstract.closedExp (G, (Ul2, IntSyn.id)) then ()
                else closedError (G, (Ul2, r))
        val U2 = Whnf.normalize (Abstract.raiseTerm (G, Ul2), IntSyn.id)
        val V2 = Whnf.normalize (Abstract.raiseType (G, Vl2), IntSyn.id)
        val _ = if !Global.doubleCheck
                  then ((Timers.time Timers.checking TypeCheck.check) (V2, IntSyn.Uni level2);
                        (Timers.time Timers.checking TypeCheck.check) (U2, V2);
                        (Timers.time Timers.checking TypeCheck.checkConv) (V1, V2);
                        case U1Opt
                          of NONE => ()
                           | SOME U1 => 
                        (Timers.time Timers.checking TypeCheck.checkConv) (U1, U2))
                else ()
      in
        IntSyn.AbbrevDef (name, parent, i1, U2, V2, level2)
      end

end; (* functor TpRecon *)
