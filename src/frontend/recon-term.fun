(* Type Reconstruction with Tracing *)
(* Author: Kevin Watkins *)
(* Based on a previous implementation by Frank Pfenning *)
(* with modifications by Jeff Polakow and Roberto Virga *)

(* ------------------- *)
(* Type Reconstruction *)
(* ------------------- *)

functor ReconTerm ((*! structure IntSyn' : INTSYN !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = IntSyn' !*)
                   (*! structure Paths' : PATHS !*)
                   structure Approx : APPROX
                   (*! sharing Approx.IntSyn = IntSyn' !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn' !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn' !*)
                   structure Abstract : ABSTRACT
                   (*! sharing Abstract.IntSyn = IntSyn' !*)
                   structure Print : PRINT
                   (*! sharing Print.IntSyn = IntSyn' !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn' !*)
                   structure StringTree : TABLE where type key = string
                   structure Msg : MSG)
  : RECON_TERM =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  structure F = Print.Formatter
  structure Apx = Approx

  (* Error handling *)

  val delayedList : (unit -> unit) list ref = ref nil

  fun clearDelayed () = (delayedList := nil)
  fun addDelayed f = (delayedList := f::(!delayedList))
  fun runDelayed () =
      let
        fun run' nil = ()
          | run' (h::t) = (run' t; h ())
      in
        run' (!delayedList)
      end

  exception Error of string

  val errorCount = ref 0
  val errorFileName = ref "no file"

  val errorThreshold = ref (SOME (20))
  fun exceeds (i, NONE) = false
    | exceeds (i, SOME(j)) = i > j

  fun resetErrors (fileName) =
      (errorCount := 0;
       errorFileName := fileName)

  fun die (r) =
        raise Error (Paths.wrap (r,
                     " " ^ Int.toString (!errorCount)
                     ^ " error" ^ (if !errorCount > 1 then "s" else "")
                     ^ " found"))

  fun checkErrors (r) =
       if !errorCount > 0 then die (r) else ()

  (* Since this structure uses a non-standard error reporting mechanism,
     any errors reported here while chatter = 1 will be printed
     in between the "[Loading file ..." message and the closing "]",
     instead of after the closing "]".  If we don't emit a newline
     when chatter = 1, the first such error will appear on the same line
     as "[Loading file ...", terribly confusing the Emacs error parsing code.
   *)
  fun chatterOneNewline () =
      if !Global.chatter = 1 andalso !errorCount = 1
        then Msg.message "\n"
      else ()

  fun fatalError (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       die (r))

  fun error (r, msg) =
      (errorCount := !errorCount + 1;
       chatterOneNewline ();
       Msg.message (!errorFileName ^ ":" ^ Paths.wrap (r, msg) ^ "\n");
       if exceeds (!errorCount, !errorThreshold)
          then die (r)
       else ())

  fun formatExp (G, U) =
      Print.formatExp (G, U)
      handle Names.Unprintable => F.String "%_unprintable_%"

  (* this is a hack, i know *)
  val queryMode = ref false

  local
    open IntSyn
  in

  fun headConDec (Const c) = sgnLookup c
    | headConDec (Skonst c) = sgnLookup c
    | headConDec (Def d) = sgnLookup d
    | headConDec (NSDef d) = sgnLookup d
    | headConDec (FgnConst (_, cd)) = cd
      (* others impossible by invariant *)

  (* lowerType (G, (V, s)) = (G', a)
     if   G0 |- V : type and G |- s : G0
     and  G |- V[s] = {{G1}} a : type
     then G' = G, G1 *)
  fun lowerTypeW (G, (Pi ((D, _), V), s)) =
      let
        val D' = decSub (D, s)
      in
        lowerType (Decl (G, D'), (V, dot1 s))
      end
    | lowerTypeW (G, Vs) = (G, EClo Vs)
  and lowerType (G, Vs) = lowerTypeW (G, Whnf.whnfExpandDef Vs)

  (* raiseType (G, V) = {{G}} V *)
  fun raiseType (Null, V) = V
    | raiseType (Decl (G, D), V) = raiseType (G, Pi ((D, Maybe), V))

  end (* open IntSyn *)

  local
    val evarApxTable : Apx.Exp StringTree.Table = StringTree.new (0)
    val fvarApxTable : Apx.Exp StringTree.Table = StringTree.new (0)

    val fvarTable : IntSyn.Exp StringTree.Table = StringTree.new (0)
  in

    fun varReset () = (StringTree.clear evarApxTable;
                       StringTree.clear fvarApxTable;
                       StringTree.clear fvarTable)

    fun getEVarTypeApx name =
        (case StringTree.lookup evarApxTable name
           of SOME V => V
            | NONE =>
        (case Names.getEVarOpt name
           of SOME (IntSyn.EVar (_, _, V, _)) =>
              let
                val (V', _ (* Type *)) = Apx.classToApx (V)
              in
                StringTree.insert evarApxTable (name, V');
                V'
              end
            | NONE =>
              let
                val V = Apx.newCVar ()
              in
                StringTree.insert evarApxTable (name, V);
                V
              end))

    fun getFVarTypeApx name =
        (case StringTree.lookup fvarApxTable name
           of SOME V => V
            | NONE =>
              let
                val V = Apx.newCVar ()
              in
                StringTree.insert fvarApxTable (name, V);
                V
              end)

    fun getEVar (name, allowed) =
        (case Names.getEVarOpt name
           of SOME (X as IntSyn.EVar (_, G, V, _)) => (X, raiseType (G, V))
            | NONE =>
              let
                val V = Option.valOf (StringTree.lookup evarApxTable name)
                val V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed)
                val (G'', V'') = lowerType (IntSyn.Null, (V', IntSyn.id))
                val X = IntSyn.newEVar (G'', V'')
              in
                Names.addEVar (X, name);
                (X, V')
              end)

    fun getFVarType (name, allowed) =
        (case StringTree.lookup fvarTable name
           of SOME V => V
            | NONE =>
              let
                val V = Option.valOf (StringTree.lookup fvarApxTable name)
                val V' = Apx.apxToClass (IntSyn.Null, V, Apx.Type, allowed)
              in
                StringTree.insert fvarTable (name, V');
                V'
              end)

  end

  (* External syntax of terms *)

  datatype term =
      internal of IntSyn.Exp * IntSyn.Exp * Paths.region (* (U, V, r) *)
        (* G |- U : V nf where V : L or V == kind *)
        (* not used currently *)

    | constant of IntSyn.Head * Paths.region
        (* must be Const/Skonst/Def/NSDef/FgnConst *)
    | bvar of int * Paths.region
    | evar of string * Paths.region
    | fvar of string * Paths.region
    | typ of Paths.region
    | arrow of term * term
    | pi of dec * term
    | lam of dec * term
    | app of term * term
    | hastype of term * term
    | mismatch of term * term * string * string
        (* (original, replacement, location, problem) *)

      (* Phase 1 only *)
    | omitted of Paths.region
    | lcid of string list * string * Paths.region
    | ucid of string list * string * Paths.region
    | quid of string list * string * Paths.region
    | scon of string * Paths.region

      (* Phase 2 only *)
    | omitapx of Apx.Exp * Apx.Exp * Apx.Uni * Paths.region
        (* (U, V, L, r) where U ~:~ V ~:~ L *)
        (* U undefined unless L >= kind *)

      (* Phase 3 only *)
    | omitexact of IntSyn.Exp * IntSyn.Exp * Paths.region

  and dec =
      dec of string option * term * Paths.region

  fun backarrow (tm1, tm2) = arrow (tm2, tm1)

  (* for now *)
  fun dec0 (nameOpt, r) = dec (nameOpt, omitted (r), r)

  datatype job =
      jnothing
    | jand of job * job
    | jwithctx of dec IntSyn.Ctx * job
    | jterm of term
    | jclass of term
    | jof of term * term
    | jof' of term * IntSyn.Exp

  fun termRegion (internal (U, V, r)) = r
    | termRegion (constant (H, r)) = r
    | termRegion (bvar (k, r)) = r
    | termRegion (evar (name, r)) = r
    | termRegion (fvar (name, r)) = r
    | termRegion (typ (r)) = r
    | termRegion (arrow (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2)
    | termRegion (pi (tm1, tm2)) =
        Paths.join (decRegion tm1, termRegion tm2)
    | termRegion (lam (tm1, tm2)) =
        Paths.join (decRegion tm1, termRegion tm2)
    | termRegion (app (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2)
    | termRegion (hastype (tm1, tm2)) =
        Paths.join (termRegion tm1, termRegion tm2)
    | termRegion (mismatch (tm1, tm2, _, _)) =
        termRegion tm2
    | termRegion (omitted (r)) = r
    | termRegion (lcid (_, _, r)) = r
    | termRegion (ucid (_, _, r)) = r
    | termRegion (quid (_, _, r)) = r
    | termRegion (scon (_, r)) = r
    | termRegion (omitapx (U, V, L, r)) = r
    | termRegion (omitexact (U, V, r)) = r

  and decRegion (dec (name, tm, r)) = r

  fun ctxRegion (IntSyn.Null) = NONE
    | ctxRegion (IntSyn.Decl (g, tm)) =
        ctxRegion' (g, decRegion tm)

  and ctxRegion' (IntSyn.Null, r) = SOME r
    | ctxRegion' (IntSyn.Decl (g, tm), r) =
        ctxRegion' (g, Paths.join (r, decRegion tm))

  local
    open Apx
    datatype Ctx = datatype IntSyn.Ctx
    datatype Dec = Dec of string option * Exp | NDec of string option
  in

    (* Phase 1:
       Try to determine an approximate type/kind and level for each subterm.
       In cases where there's a mismatch, it's generally better not to report
       it immediately, but rather to wait until after the exact phase, so that
       the error message can mention more precise type information.  So instead
       the bad subterm is wrapped in a `mismatch' constructor, which also
       supplies a replacement (always an `omitted' in the current implementation)
       so that the invariant that the entire term is approximately well-typed
       after phase 1 is satisfied even in the presence of the error.
     *)

    (* inferApx (G, tm, false) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate subject
       post: tm' is an approximate subject
             U is an approximate subject
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U

       inferApx (G, tm, true) = (tm', U, V, L)
       pre: G is an approximate context
            tm is an approximate classifier
       post: tm' is an approximate classifier
             U is an approximate classifier
             V is an approximate classifier
             L is an approximate universe
             G |- U ~:~ V ~:~ L
             termToExp tm' = U
     *)

    fun filterLevel (tm, L, max, msg) =
        let
          val notGround = makeGroundUni L
          val Level i = whnfUni L
        in
          if i > max
          then fatalError (termRegion tm,
                           "Level too high\n" ^ msg)
          else if notGround
          then error (termRegion tm,
                      "Ambiguous level\n" ^
                      "The level of this term could not be inferred\n" ^
                      "Defaulting to " ^
                      (case i
                         of 1 => "object"
                          | 2 => "type family"
                          | 3 => "kind") ^
                      " level")
          else ()
        end

    fun findOmitted (G, qid, r) =
          (error (r, "Undeclared identifier "
                     ^ Names.qidToString (valOf (Names.constUndef qid)));
           omitted (r))

    fun findBVar' (Null, name, k) = NONE
      | findBVar' (Decl (G, Dec (NONE, _)), name, k) =
          findBVar' (G, name, k+1)
      | findBVar' (Decl (G, NDec _), name, k) =
          findBVar' (G, name, k+1)
      | findBVar' (Decl (G, Dec (SOME(name'), _)), name, k) =
          if name = name' then SOME (k)
          else findBVar' (G, name, k+1)

    fun findBVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case findBVar' (G, name, 1)
                 of NONE => fc (G, qid, r)
                  | SOME k => bvar (k, r)))

    fun findConst fc (G, qid, r) =
        (case Names.constLookup qid
           of NONE => fc (G, qid, r)
            | SOME cid =>
              (case IntSyn.sgnLookup cid
                 of IntSyn.ConDec _ => constant (IntSyn.Const cid, r)
                  | IntSyn.ConDef _ => constant (IntSyn.Def cid, r)
                  | IntSyn.AbbrevDef _ => constant (IntSyn.NSDef cid, r)
                  | _ =>
                    (error (r, "Invalid identifier\n"
                            ^ "Identifier `" ^ Names.qidToString qid
                            ^ "' is not a constant, definition or abbreviation");
                     omitted (r))))

    fun findCSConst fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name =>
              (case CSManager.parse name
                 of NONE => fc (G, qid, r)
                  | SOME (cs, conDec) =>
                      constant (IntSyn.FgnConst (cs, conDec), r)))

    fun findEFVar fc (G, qid, r) =
        (case Names.unqualified qid
           of NONE => fc (G, qid, r)
            | SOME name => (if !queryMode then evar else fvar) (name, r))

    fun findLCID x = findBVar (findConst (findCSConst findOmitted)) x
    fun findUCID x = findBVar (findConst (findCSConst (findEFVar findOmitted))) x
    fun findQUID x = findConst (findCSConst findOmitted) x


    fun inferApx (G, tm as internal (U, V, r)) =
        let
          val (U', V', L') = exactToApx (U, V)
        in
          (tm, U', V', L')
        end

      | inferApx (G, tm as lcid (ids, name, r)) =
        let
          val qid = Names.Qid (ids, name)
        in
          inferApx (G, findLCID (G, qid, r))
        end
      | inferApx (G, tm as ucid (ids, name, r)) =
        let
          val qid = Names.Qid (ids, name)
        in
          inferApx (G, findUCID (G, qid, r))
        end
      | inferApx (G, tm as quid (ids, name, r)) =
        let
          val qid = Names.Qid (ids, name)
        in
          inferApx (G, findQUID (G, qid, r))
        end
      | inferApx (G, tm as scon (name, r)) =
          (case CSManager.parse name
             of NONE => (error (r, "Strings unsupported in current signature");
                         inferApx (G, omitted (r)))
              | SOME (cs, conDec) =>
                  inferApx (G, constant (IntSyn.FgnConst (cs, conDec), r)))

      | inferApx (G, tm as constant (H, r)) =
        let
          val cd = headConDec H
          val (U', V', L') = exactToApx (IntSyn.Root (H, IntSyn.Nil),
                                         IntSyn.conDecType cd)
          fun dropImplicit (V, 0) = V
            | dropImplicit (Arrow (_, V), i) = dropImplicit (V, i-1)
          val V'' = dropImplicit (V', IntSyn.conDecImp cd)
        in
          (tm, U', V'', L')
        end
      | inferApx (G, tm as bvar (k, r)) =
        let
          val Dec (_, V) = IntSyn.ctxLookup (G, k)
        in
          (tm, Undefined, V, Type)
        end
      | inferApx (G, tm as evar (name, r)) =
          (tm, Undefined, getEVarTypeApx name, Type)
      | inferApx (G, tm as fvar (name, r)) =
          (tm, Undefined, getFVarTypeApx name, Type)
      | inferApx (G, tm as typ (r)) =
          (tm, Uni Type, Uni Kind, Hyperkind)
      | inferApx (G, arrow (tm1, tm2)) =
        let
          val L = newLVar ()
          val (tm1', V1) = checkApx (G, tm1, Uni Type, Kind,
                                     "Left-hand side of arrow must be a type")
          val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of arrow must be a type or a kind")
        in
          (arrow (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end
      | inferApx (G, pi (tm1, tm2)) =
        let
          val (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1)
          val L = newLVar ()
          val (tm2', V2) = checkApx (Decl (G, D), tm2, Uni L, Next L,
                                     "Body of pi must be a type or a kind")
        in
          (pi (tm1', tm2'), Arrow (V1, V2), Uni L, Next L)
        end
      | inferApx (G, tm as lam (tm1, tm2)) =
        let
          val (tm1', D as Dec (_, V1)) = inferApxDec (G, tm1)
          val (tm2', U2, V2, L2) = inferApx (Decl (G, D), tm2)
        in
          (lam (tm1', tm2'), U2, Arrow (V1, V2), L2)
        end
      | inferApx (G, tm as app (tm1, tm2)) =
        let
          val L = newLVar ()
          val Va = newCVar ()
          val Vr = newCVar ()
          val (tm1', U1) = checkApx (G, tm1, Arrow (Va, Vr), L,
                                     "Non-function was applied to an argument")
          (* probably a confusing message if the problem is the level: *)
          val (tm2', _) = checkApx (G, tm2, Va, Type,
                                    "Argument type did not match function domain type")
        in
          (app (tm1', tm2'), U1, Vr, L)
        end
      | inferApx (G, tm as hastype (tm1, tm2)) =
        let
          val L = newLVar ()
          val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "Right-hand side of ascription must be a type or a kind")
          val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription did not hold")
          val _ = addDelayed (fn () => filterLevel (tm, L, 2, "Ascription can only be applied to objects and type families"))
        in
          (hastype (tm1', tm2'), U1, V2, L)
        end
      | inferApx (G, omitted (r)) =
        let
          val L = newLVar ()
          val V = newCVar ()
          val U = newCVar () (* guaranteed not to be used if L is type *)
        in
          (omitapx (U, V, L, r), U, V, L)
        end

    and checkApx (G, tm, V, L, location_msg) =
        let
          val (tm', U', V', L') = inferApx (G, tm)
        in
          (matchUni (L, L'); match (V, V'); (tm', U'))
          handle Unify problem_msg =>
          let
            val r = termRegion tm
            val (tm'', U'') = checkApx (G, omitted (r), V, L, location_msg)
            (* just in case *)
            val _ = addDelayed (fn () => (makeGroundUni L'; ()))
          in
            (mismatch (tm', tm'', location_msg, problem_msg), U'')
          end
        end

    and inferApxDec (G, dec (name, tm, r)) =
        let
          val (tm', V1) = checkApx (G, tm, Uni Type, Kind,
                                    "Classifier in declaration must be a type")
          val D = Dec (name, V1)
        in
          (dec (name, tm', r), D)
        end

    fun inferApxJob (G, jnothing) = jnothing
      | inferApxJob (G, jand (j1, j2)) =
          jand (inferApxJob (G, j1), inferApxJob (G, j2))
      | inferApxJob (G, jwithctx (g, j)) =
        let
          fun ia (Null) = (G, Null)
            | ia (Decl (g, tm)) =
              let
                val (G', g') = ia (g)
                val _ = clearDelayed ()
                val (tm', D) = inferApxDec (G', tm)
                val _ = runDelayed ()
              in
                (Decl (G', D), Decl (g', tm'))
              end
          val (G', g') = ia (g)
        in
          jwithctx (g', inferApxJob (G', j))
        end
      | inferApxJob (G, jterm (tm)) =
        let
          val _ = clearDelayed ()
          val (tm', U, V, L) = inferApx (G, tm)
          val _ = filterLevel (tm', L, 2,
                               "The term in this position must be an object or a type family")
          val _ = runDelayed ()
        in
          jterm (tm')
        end
      | inferApxJob (G, jclass (tm)) =
        let
          val _ = clearDelayed ()
          val L = newLVar ()
          val (tm', V) = checkApx (G, tm, Uni L, Next L,
                                   "The term in this position must be a type or a kind")
          val _ = filterLevel (tm', Next L, 3,
                               "The term in this position must be a type or a kind")
          val _ = runDelayed ()
        in
          jclass (tm')
        end
      | inferApxJob (G, jof (tm1, tm2)) =
        let
          val _ = clearDelayed ()
          val L = newLVar ()
          val (tm2', V2) = checkApx (G, tm2, Uni L, Next L,
                                     "The term in this position must be a type or a kind")
          val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold")
          val _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family")
          val _ = runDelayed ()
        in
          jof (tm1', tm2')
        end
      | inferApxJob (G, jof' (tm1, V)) =
        let
          val _ = clearDelayed ()
          val L = newLVar ()
          val (V2, _) = Apx.classToApx V
          val (tm1', U1) = checkApx (G, tm1, V2, L,
                                     "Ascription in declaration did not hold")
          val _ = filterLevel (tm1', L, 2,
                               "The term in this position must be an object or a type family")
          val _ = runDelayed ()
        in
          jof' (tm1', V)
        end

    fun ctxToApx IntSyn.Null = IntSyn.Null
      | ctxToApx (IntSyn.Decl (G, IntSyn.NDec x)) =
          IntSyn.Decl (ctxToApx G, NDec x)
      | ctxToApx (IntSyn.Decl (G, IntSyn.Dec (name, V))) =
          let
            val (V', _) = Apx.classToApx V
          in
            IntSyn.Decl (ctxToApx G, Dec (name, V'))
          end

    fun inferApxJob' (G, t) =
        inferApxJob (ctxToApx G, t)

  end (* open Apx *)

  local
    open IntSyn
  in

  (* Final reconstruction job syntax *)

  datatype Job =
      JNothing
    | JAnd of Job * Job
    | JWithCtx of IntSyn.Dec IntSyn.Ctx * Job
    | JTerm of (IntSyn.Exp * Paths.occExp) * IntSyn.Exp * IntSyn.Uni
    | JClass of (IntSyn.Exp * Paths.occExp) * IntSyn.Uni
    | JOf of (IntSyn.Exp * Paths.occExp) * (IntSyn.Exp * Paths.occExp) * IntSyn.Uni

  (* This little datatype makes it easier to work with eta-expanded terms
     The idea is that Elim E represents a term U if
       E (s, S) = U[s] @ S *)

  datatype Bidi =
      Elim of IntSyn.Sub * IntSyn.Spine -> IntSyn.Exp
    | Intro of IntSyn.Exp

  fun elimSub (E, s) = (fn (s', S) => E (comp (s, s'), S))
  fun elimApp (E, U) = (fn (s, S) => E (s, App (EClo (U, s), S)))

  fun bvarElim (n) = (fn (s, S) =>
      (case bvarSub (n, s)
         of Idx (n') => Root (BVar n', S)
          | Exp (U) => Redex (U, S)))
  fun fvarElim (name, V, s) =
        (fn (s', S) => Root (FVar (name, V, comp (s, s')), S))
  fun redexElim (U) = (fn (s, S) => Redex (EClo (U, s), S))
  (* headElim (H) = E
     assumes H not Proj _ *)
  fun headElim (BVar n) = bvarElim n
    | headElim (FVar fv) = fvarElim fv
    | headElim (NSDef d) = redexElim (constDef d)
    | headElim (H) =
      (case conDecStatus (headConDec H)
         of Foreign (csid, f) => (fn (s, S) => f S)
          | _ => (fn (s, S) => Root (H, S)))
  (* although internally EVars are lowered intro forms, externally they're
     raised elim forms.
     this conforms to the external interpretation:
     the type of the returned elim form is ([[G]] V) *)
  fun evarElim (X as EVar _) =
        (fn (s, S) => EClo (X, Whnf.spineToSub (S, s)))

  fun etaExpandW (E, (Pi ((D as Dec (_, Va), _), Vr), s)) =
      let
        val U1 = etaExpand (bvarElim (1), (Va, comp (s, shift)))
        val D' = decSub (D, s)
      in
        Lam (D', etaExpand (elimApp (elimSub (E, shift), U1), (Vr, dot1 s)))
      end
    | etaExpandW (E, _) = E (id, Nil)
  and etaExpand (E, Vs) = etaExpandW (E, Whnf.whnfExpandDef Vs)

  (* preserves redices *)
  fun toElim (Elim E) = E
    | toElim (Intro U) = redexElim U

  fun toIntro (Elim E, Vs) = etaExpand (E, Vs)
    | toIntro (Intro U, Vs) = U

  fun addImplicit1W (G, E, (Pi ((Dec (_, Va), _), Vr), s), i (* >= 1 *)) =
      let
        val X = Whnf.newLoweredEVar (G, (Va, s))
      in
        addImplicit (G, elimApp (E, X), (Vr, Whnf.dotEta (Exp (X), s)), i-1)
      end

      (* if no implicit arguments, do not expand Vs!!! *)
  and addImplicit (G, E, Vs, 0) = (E, EClo Vs)
    | addImplicit (G, E, Vs, i) = addImplicit1W (G, E, Whnf.whnfExpandDef Vs, i)


  (* Report mismatches after the entire process finishes -- yields better
     error messages *)

  fun reportConstraints (Xnames) =
      (case Print.evarCnstrsToStringOpt (Xnames)
         of NONE => ()
          | SOME(constr) => print ("Constraints:\n" ^ constr ^ "\n"))
      handle Names.Unprintable => print "%_constraints unprintable_%\n"

  fun reportInst (Xnames) =
      (Msg.message (Print.evarInstToString (Xnames) ^ "\n"))
      handle Names.Unprintable => Msg.message "%_unifier unprintable_%\n"

  fun delayMismatch (G, V1, V2, r2, location_msg, problem_msg) =
      addDelayed (fn () =>
      let
        val Xs = Abstract.collectEVars (G, (V2, id),
                 Abstract.collectEVars (G, (V1, id), nil))
        val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
        val V1fmt = formatExp (G, V1)
        val V2fmt = formatExp (G, V2)
        val diff = F.Vbox0 0 1
                   [F.String "Expected:", F.Space, V2fmt, F.Break,
                    F.String "Inferred:", F.Space, V1fmt]
        val diff = (case Print.evarCnstrsToStringOpt (Xnames)
                      of NONE => F.makestring_fmt diff
                       | SOME(cnstrs) => F.makestring_fmt diff ^
                                         "\nConstraints:\n" ^ cnstrs)
      in
        error (r2, "Type mismatch\n"
                   ^ diff ^ "\n"
                   ^ problem_msg ^ "\n"
                   ^ location_msg)
      end)

  fun delayAmbiguous (G, U, r, msg) =
      addDelayed (fn () =>
      let
        val Ufmt = formatExp (G, U)
        val amb = F.HVbox [F.String "Inferred:", F.Space, formatExp (G, U)]
      in
        error (r, "Ambiguous reconstruction\n"
                  ^ F.makestring_fmt amb ^ "\n"
                  ^ msg)
      end)

  fun unifyIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        val _ = Unify.reset ()
        val _ = Unify.unify x
                handle e as Unify.Unify _ =>
                       (Unify.unwind ();
                        raise e)
        val _ = Unify.reset ()
      in
        ()
      end

  fun unifiableIdem x =
      let
        (* this reset should be unnecessary -- for safety only *)
        val _ = Unify.reset ()
        val ok = Unify.unifiable x
        val _ = if ok then Unify.reset () else Unify.unwind ()
      in
        ok
      end

  (* tracing code *)

  datatype TraceMode = Progressive | Omniscient
  val trace = ref false
  val traceMode = ref Omniscient

  fun report f = case !traceMode of Progressive => f ()
                                  | Omniscient => addDelayed f

  fun reportMismatch (G, Vs1, Vs2, problem_msg) =
      report (fn () =>
      let
        val Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil))
        val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
        val eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)]
        val _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n")
        val _ = reportConstraints Xnames
        val _ = Msg.message ("Failed: " ^ problem_msg ^ "\n"
                       ^ "Continuing with subterm replaced by _\n")
      in
        ()
      end)

  fun reportUnify' (G, Vs1, Vs2) =
      let
        val Xs = Abstract.collectEVars (G, Vs2,
                 Abstract.collectEVars (G, Vs1, nil))
        val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
        val eqnsFmt = F.HVbox [F.String "|?", F.Space, formatExp (G, EClo Vs1),
                               F.Break, F.String "=", F.Space, formatExp (G, EClo Vs2)]
        val _ = Msg.message (F.makestring_fmt eqnsFmt ^ "\n")
        val _ = unifyIdem (G, Vs1, Vs2)
                handle e as Unify.Unify msg =>
                       (Msg.message ("Failed: " ^ msg ^ "\n"
                               ^ "Continuing with subterm replaced by _\n");
                        raise e)
        val _ = reportInst Xnames
        val _ = reportConstraints Xnames
      in
        ()
      end

  fun reportUnify (G, Vs1, Vs2) =
        (case !traceMode
           of Progressive => reportUnify' (G, Vs1, Vs2)
            | Omniscient =>
                (unifyIdem (G, Vs1, Vs2)
                 handle e as Unify.Unify msg =>
                   (reportMismatch (G, Vs1, Vs2, msg);
                    raise e)))

  fun reportInfer' (G, omitexact (_, _, r), U, V) =
      let
        val Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil))
        val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
        val omit = F.HVbox [F.String "|-", F.Space, F.String "_", F.Space,
                            F.String "==>", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)]
        val _ = Msg.message (F.makestring_fmt omit ^ "\n")
        val _ = reportConstraints Xnames
      in
        ()
      end
    | reportInfer' (G, mismatch (tm1, tm2, _, _), U, V) =
        reportInfer' (G, tm2, U, V)
    | reportInfer' (G, hastype _, U, V) = ()
    | reportInfer' (G, tm, U, V) =
      let
        val Xs = Abstract.collectEVars (G, (U, id),
                 Abstract.collectEVars (G, (V, id), nil))
        val Xnames = List.map (fn X => (X, Names.evarName (IntSyn.Null, X))) Xs
        val judg = F.HVbox [F.String "|-", F.Space, formatExp (G, U), F.Break,
                            F.String ":", F.Space, formatExp (G, V)]
        val _ = Msg.message (F.makestring_fmt judg ^ "\n")
        val _ = reportConstraints Xnames
      in
        ()
      end

  fun reportInfer x = report (fn () => reportInfer' x)


    (* inferExact (G, tm) = (tm', U, V)
       if  tm is approximately well typed
       and tm contains no subterm above kind level
       and tm ~:~ V1
       then tm = U-
       and  U : V
       and  U, V are most general such
       effect: as for unification *)

    fun inferExactN (G, tm as internal (U, V, r)) =
          (tm, Intro U, V)
      | inferExactN (G, tm as constant (H, r)) =
        let
          val cd = headConDec (H)
          val (E, V) = addImplicit (G, headElim H, (conDecType cd, id), conDecImp cd)
        in
          (tm, Elim E, V)
        end
      | inferExactN (G, tm as bvar (k, r)) =
        let
          val Dec (_, V) = ctxDec (G, k)
        in
          (tm, Elim (bvarElim k), V)
        end
      | inferExactN (G, tm as evar (name, r)) =
        let
          (* externally EVars are raised elim forms *)
          val (X, V) = getEVar (name, false)
                  handle Apx.Ambiguous =>
                  let
                    val (X, V) = getEVar (name, true)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    (X, V)
                  end
          val s = Shift (ctxLength (G)) (* necessary? -kw *)
        in
          (tm, Elim (elimSub (evarElim X, s)), EClo (V, s))
        end
      | inferExactN (G, tm as fvar (name, r)) =
        let
          val V = getFVarType (name, false)
                  handle Apx.Ambiguous =>
                  let
                    val V = getFVarType (name, true)
                  in
                    delayAmbiguous (G, V, r, "Free variable has ambiguous type");
                    V
                  end
          val s = Shift (ctxLength (G)) (* necessary? -kw *)
        in
          (tm, Elim (fvarElim (name, V, s)), EClo (V, s))
        end
      | inferExactN (G, tm as typ (r)) =
          (tm, Intro (Uni Type), Uni Kind)
      | inferExactN (G, arrow (tm1, tm2)) =
        let
          val (tm1', B1, _ (* Uni Type *)) = inferExact (G, tm1)
          val D = Dec (NONE, toIntro (B1, (Uni Type, id)))
          val (tm2', B2, L) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L, id))
        in
          (arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L)
        end
      | inferExactN (G, pi (tm1, tm2)) =
        let
          val (tm1', D) = inferExactDec (G, tm1)
          val (tm2', B2, L) = inferExact (Decl (G, D), tm2)
          val V2 = toIntro (B2, (L, id))
        in
          (pi (tm1', tm2'), Intro (Pi ((D, Maybe), V2)), L)
        end
      | inferExactN (G, lam (tm1, tm2)) =
        let
          val (tm1', D) = inferExactDec (G, tm1)
          val (tm2', B2, V2) = inferExact (Decl (G, D), tm2)
          val U2 = toIntro (B2, (V2, id))
        in
          (lam (tm1', tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2))
        end
      | inferExactN (G, app (tm1, tm2)) =
        let
          val (tm1', B1, V1) = inferExact (G, tm1)
          val E1 = toElim (B1)
          val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef (V1, id)
          val (tm2', B2) = checkExact (G, tm2, (Va, s),
                                       "Argument type did not match function domain type\n(Index object(s) did not match)")
          val U2 = toIntro (B2, (Va, s))
        in
          (app (tm1', tm2'), Elim (elimApp (E1, U2)), EClo (Vr, Whnf.dotEta (Exp U2, s)))
        end
      | inferExactN (G, hastype (tm1, tm2)) =
        let
          val (tm2', B2, L) = inferExact (G, tm2)
          val V = toIntro (B2, (L, id))
          val (tm1', B1) = checkExact (G, tm1, (V, id),
                                      "Ascription did not hold\n(Index object(s) did not match)")
        in
          (hastype (tm1', tm2'), B1, V)
        end
      | inferExactN (G, mismatch (tm1, tm2, location_msg, problem_msg)) =
        let
          val (tm1', _, V1) = inferExact (G, tm1)
          val (tm2', B, V) = inferExactN (G, tm2)
          val _ = if !trace then reportMismatch (G, (V1, id), (V, id), problem_msg) else ()
          val _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
          (mismatch (tm1', tm2', location_msg, problem_msg), B, V)
        end
      | inferExactN (G, omitapx (U, V, L, r)) =
        let
          val V' = Apx.apxToClass (G, V, L, false)
                   handle Apx.Ambiguous =>
                   let
                     val V' = Apx.apxToClass (G, V, L, true)
                   in
                     delayAmbiguous (G, V', r, "Omitted term has ambiguous " ^
                       (case Apx.whnfUni L
                          of Apx.Level 1 => "type"
                           | Apx.Level 2 => "kind"
                             (* yes, this can happen in pathological cases, e.g.
                                  a : type. b = a : _ _. *)
                             (* FIX: this violates an invariant in printing *)
                           | Apx.Level 3 => "hyperkind"));
                     V'
                   end
          val U' = Apx.apxToExact (G, U, (V', id), false)
                   handle Apx.Ambiguous =>
                   let
                     val U' = Apx.apxToExact (G, U, (V', id), true)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end
        in
          (omitexact (U', V', r), Intro U', V')
        end

    and inferExact (G, tm) =
        if not (!trace) then inferExactN (G, tm)
        else
        let
          val (tm', B', V') = inferExactN (G, tm)
        in
          reportInfer (G, tm', toIntro (B', (V', id)), V');
          (tm', B', V')
        end

    and inferExactDec (G, dec (name, tm, r)) =
        let
          val (tm', B1, _ (* Uni Type *)) = inferExact (G, tm)
          val V1 = toIntro (B1, (Uni Type, id))
          val D = Dec (name, V1)
        in
          (dec (name, tm', r), D)
        end

    and checkExact1 (G, lam (dec (name, tm1, r), tm2), Vhs) =
        let
          val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          val V1 = toIntro (B1, (Uni Type, id))
          val D = Dec (name, V1)
          val ((tm2', B2, V2), ok2) =
                if ok1 then checkExact1 (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false)
          val U2 = toIntro (B2, (V2, id))
        in
          ((lam (dec (name, tm1', r), tm2'), Intro (Lam (D, U2)), Pi ((D, Maybe), V2)), ok2)
        end
      | checkExact1 (G, hastype (tm1, tm2), Vhs) =
        let
          val ((tm2', B2, L), ok2) = unifyExact (G, tm2, Vhs)
          val V = toIntro (B2, (L, id))
          val (tm1', B1) = checkExact (G, tm1, (V, id),
                                       "Ascription did not hold\n(Index object(s) did not match)")
        in
          ((hastype (tm1', tm2'), B1, V), ok2)
        end
      | checkExact1 (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          val (tm1', _, V1) = inferExact (G, tm1)
          val ((tm2', B, V), ok2) = checkExact1 (G, tm2, Vhs)
          val _ = delayMismatch (G, V1, V, termRegion tm2', location_msg, problem_msg)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, V), ok2)
        end
      | checkExact1 (G, omitapx (U, V (* = Vhs *), L, r), Vhs) =
        let
          val V' = EClo Vhs
          val U' = Apx.apxToExact (G, U, Vhs, false)
                   handle Apx.Ambiguous =>
                   let
                     val U' = Apx.apxToExact (G, U, Vhs, true)
                   in
                     delayAmbiguous (G, U', r, "Omitted " ^
                       (case Apx.whnfUni L
                          of Apx.Level 2 => "type"
                           | Apx.Level 3 => "kind") ^ " is ambiguous");
                     U'
                   end
        in
          ((omitexact (U', V', r), Intro U', V'), true)
        end
      | checkExact1 (G, tm, Vhs) =
        let
          val (tm', B', V') = inferExact (G, tm)
        in
          ((tm', B', V'), unifiableIdem (G, Vhs, (V', id)))
        end

    and checkExact (G, tm, Vs, location_msg) =
        if not (!trace) then
        let
          val ((tm', B', V'), ok) = checkExact1 (G, tm, Vs)
        in
          if ok then (tm', B')
          else
          ((unifyIdem (G, (V', id), Vs);
            raise Match (* can't happen *))
           handle Unify.Unify problem_msg =>
           let
             val r = termRegion tm
             val U' = toIntro (B', (V', id))
             val (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V')
             val ((tm'', B'', _ (* Vs *)), _ (* true *)) =
                   checkExact1 (G, omitapx (Uapx, Vapx, Lapx, r), Vs)
             val _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg)
           in
             (mismatch (tm', tm'', location_msg, problem_msg), B'')
           end)
        end

        else
        let
          val (tm', B', V') = inferExact (G, tm)
        in
          (reportUnify (G, (V', id), Vs); (tm', B'))
          handle Unify.Unify problem_msg =>
          let
            val r = termRegion tm
            val U' = toIntro (B', (V', id))
            val (Uapx, Vapx, Lapx) = Apx.exactToApx (U', V')
            val (tm'', B'') =
                  checkExact (G, omitapx (Uapx, Vapx, Lapx, r), Vs, location_msg)
            val _ = delayMismatch (G, V', EClo Vs, r, location_msg, problem_msg)
          in
            (mismatch (tm', tm'', location_msg, problem_msg), B'')
          end
        end

    and unifyExact (G, arrow (tm1, tm2), Vhs) =
        let
          val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          val V1 = toIntro (B1, (Uni Type, id))
          val D = Dec (NONE, V1)
          val (tm2', B2, L) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L, id))
        in
          ((arrow (tm1', tm2'), Intro (Pi ((D, No), EClo (V2, shift))), L),
           ok1 andalso unifiableIdem (Decl (G, D), (Vr, dot1 s), (V2, shift)))
        end
      | unifyExact (G, pi (dec (name, tm1, r), tm2), Vhs) =
        let
          val (Pi ((Dec (_, Va), _), Vr), s) = Whnf.whnfExpandDef Vhs
          val ((tm1', B1, _ (* Uni Type *)), ok1) = unifyExact (G, tm1, (Va, s))
          val V1 = toIntro (B1, (Uni Type, id))
          val D = Dec (name, V1)
          val ((tm2', B2, L), ok2) =
                if ok1 then unifyExact (Decl (G, D), tm2, (Vr, dot1 s))
                else (inferExact (Decl (G, D), tm2), false)
          val V2 = toIntro (B2, (L, id))
        in
          ((pi (dec (name, tm1', r), tm2'), Intro (Pi ((D, Maybe), V2)), L), ok2)
        end
        (* lam impossible *)
      | unifyExact (G, hastype (tm1, tm2), Vhs) =
        let
          (* Vh : L by invariant *)
          val (tm2', _ (* Uni L *), _ (* Uni (Next L) *)) = inferExact (G, tm2)
          val ((tm1', B, L), ok1) = unifyExact (G, tm1, Vhs)
        in
          ((hastype (tm1', tm2'), B, L), ok1)
        end
      | unifyExact (G, mismatch (tm1, tm2, location_msg, problem_msg), Vhs) =
        let
          val (tm1', _, L1) = inferExact (G, tm1)
          val ((tm2', B, L), ok2) = unifyExact (G, tm2, Vhs)
          val _ = delayMismatch (G, L1, L, termRegion tm2', location_msg, problem_msg)
        in
          ((mismatch (tm1', tm2', location_msg, problem_msg), B, L), ok2)
        end
      | unifyExact (G, omitapx (V (* = Vhs *), L, nL (* Next L *), r), Vhs) =
        let
          (* cannot raise Ambiguous *)
          val L' = Apx.apxToClass (G, L, nL, false)
          val V' = EClo Vhs
        in
          ((omitexact (V', L', r), Intro V', L'), true)
        end
      | unifyExact (G, tm, Vhs) =
        let
          val (tm', B', L') = inferExact (G, tm)
          val V' = toIntro (B', (L', id))
        in
          ((tm', B', L'), unifiableIdem (G, Vhs, (V', id)))
        end

    fun occElim (constant (H, r), os, rs, i) =
        let
          (* should probably treat a constant with Foreign
             attribute as a redex *)
          val r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, conDecImp (headConDec H), i, os), r')
        end
      | occElim (bvar (k, r), os, rs, i) =
        let
          val r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end
      | occElim (fvar (name, r), os, rs, i) =
        let
          val r' = List.foldr Paths.join r rs
        in
          (Paths.root (r', Paths.leaf r, 0, i, os), r')
        end
      | occElim (app (tm1, tm2), os, rs, i) =
        let
          val (oc2, r2) = occIntro tm2
        in
          occElim (tm1, Paths.app (oc2, os), r2::rs, i+1)
        end
      | occElim (hastype (tm1, tm2), os, rs, i) = occElim (tm1, os, rs, i)
      | occElim (tm, os, rs, i) =
        (* this is some kind of redex or evar-under-substitution
           also catches simple introduction forms like `type' *)
        let
          val r' = List.foldr Paths.join (termRegion tm) rs
        in
          (Paths.leaf r', r')
        end

    and occIntro (arrow (tm1, tm2)) =
        let
          val (oc1, r1) = occIntro tm1
          val (oc2, r2) = occIntro tm2
          val r' = Paths.join (r1, r2)
        in
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (pi (dec (name, tm1, r), tm2)) =
        let
          val (oc1, r1) = occIntro tm1
          val (oc2, r2) = occIntro tm2
          val r' = Paths.join (r, r2)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (lam (dec (name, tm1, r), tm2)) =
        let
          val (oc1, r1) = occIntro tm1
          val (oc2, r2) = occIntro tm2
          val r' = Paths.join (r, r2)
        in
          (* not quite consistent with older implementation for dec0 *)
          (Paths.bind (r', SOME oc1, oc2), r')
        end
      | occIntro (hastype (tm1, tm2)) = occIntro tm1
      | occIntro (tm) =
        let
          (* still doesn't work quite right for the location -> occurrence map? *)
          val (oc, r) = occElim (tm, Paths.nils, nil, 0)
        in
          (oc, r)
        end

    fun inferExactJob (G, jnothing) = JNothing
      | inferExactJob (G, jand (j1, j2)) =
          JAnd (inferExactJob (G, j1), inferExactJob (G, j2))
      | inferExactJob (G, jwithctx (g, j)) =
        let
          fun ie (Null) = (G, Null)
            | ie (Decl (g, tm)) =
              let
                val (G', Gresult) = ie (g)
                val (_, D) = inferExactDec (G', tm)
              in
                (Decl (G', D), Decl (Gresult, D))
              end
          val (G', Gresult) = ie (g)
        in
          JWithCtx (Gresult, inferExactJob (G', j))
        end
      | inferExactJob (G, jterm (tm)) =
        let
          val (tm', B, V) = inferExact (G, tm)
          val U = toIntro (B, (V, id))
          val (oc, r) = occIntro (tm')
          fun iu (Uni Type) = Kind
            | iu (Pi (_, V)) = iu V
            | iu (Root _) = Type
            | iu (Redex (V, _)) = iu V
            | iu (Lam (_, V)) = iu V
            | iu (EClo (V, _)) = iu V
              (* others impossible *)
        in
          JTerm ((U, oc), V, iu V)
        end
      | inferExactJob (G, jclass (tm)) =
        let
          val (tm', B, L) = inferExact (G, tm)
          val V = toIntro (B, (L, id))
          val (oc, r) = occIntro (tm')
          val (Uni L, _) = Whnf.whnf (L, id)
        in
          JClass ((V, oc), L)
        end
      | inferExactJob (G, jof (tm1, tm2)) =
        let
          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id))
          val (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)")
          val U1 = toIntro (B1, (V2, id))
          val (oc2, r2) = occIntro tm2'
          val (oc1, r1) = occIntro tm1'
          val (Uni L2, _) = Whnf.whnf (L2, id)
        in
          JOf ((U1, oc1), (V2, oc2), L2)
        end

      | inferExactJob (G, jof' (tm1, V2)) =
        let
(*          val (tm2', B2, L2) = inferExact (G, tm2)
          val V2 = toIntro (B2, (L2, id)) *)
          val (tm1', B1) = checkExact (G, tm1, (V2, id),
                                       "Ascription in declaration did not hold\n"
                                       ^ "(Index object(s) did not match)")
          val U1 = toIntro (B1, (V2, id))
(*          val (oc2, r2) = occIntro tm2' *)
          val (oc1, r1) = occIntro tm1'
(*          val (Uni L2, _) = Whnf.whnf (L2, id) *)
        in
          JOf ((U1, oc1), (V2, oc1), Type)
        end

    fun recon' (j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          val _ = Apx.varReset ()
          val _ = varReset ()
          val j' = inferApxJob (Null, j)
          val _ = clearDelayed ()
          val j'' = inferExactJob (Null, j')
          val _ = runDelayed ()
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end

    fun recon (j) = (queryMode := false; recon' j)
    fun reconQuery (j) = (queryMode := true; recon' j)

    (* Invariant, G must be named! *)
    fun reconWithCtx' (G, j) =
        let
          (* we leave it to the context to call Names.varReset
             reason: this code allows reconstructing terms containing
             existing EVars, and future developments might use that *)
          (* context must already have called resetErrors *)
          val _ = Apx.varReset ()
          val _ = varReset ()
          val j' = inferApxJob' (G, j)
          val _ = clearDelayed ()
          val j'' = inferExactJob (G, j')
          val _ = runDelayed ()
          (* we leave it to the context to call checkErrors
             reason: the caller may want to do further processing on
             the "best effort" result returned, even if there were
             errors *)
        in
          j''
        end
    fun reconWithCtx (G, j) = (queryMode := false; reconWithCtx' (G, j))
    fun reconQueryWithCtx (G, j) = (queryMode := true; reconWithCtx' (G, j))

  fun internalInst x = raise Match
  fun externalInst x = raise Match

  end (* open IntSyn *)

end; (* functor ReconTerm *)
