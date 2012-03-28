(* Total Declarations *)
(* Author: Frank Pfenning *)

functor Total
  (structure Global : GLOBAL
   structure Table : TABLE where type key = int

   (*! structure IntSyn' : INTSYN !*)
   structure Whnf : WHNF
   (*! sharing Whnf.IntSyn = IntSyn' !*)

   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)

   structure ModeTable : MODETABLE
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure ModeCheck : MODECHECK

   structure Index : INDEX
   (*! sharing Index.IntSyn = IntSyn' !*)

   structure Subordinate : SUBORDINATE
   (*! sharing Subordinate.IntSyn = IntSyn' !*)

   structure Order : ORDER
   (*! sharing Order.IntSyn = IntSyn' !*)
   structure Reduces : REDUCES
   (*! sharing Reduces.IntSyn = IntSyn' !*)

   structure Cover : COVER

     (*! structure Paths : PATHS !*)
   structure Origins : ORIGINS
   (*! sharing Origins.Paths = Paths !*)
     (*! sharing Origins.IntSyn = IntSyn' !*)

   structure Timers : TIMERS)
   : TOTAL =
struct
  (*! structure IntSyn = IntSyn' !*)

  exception Error of string

  local
    structure I = IntSyn
    structure P = Paths
    structure M = ModeSyn
    structure N = Names

    (* totalTable (a) = SOME() iff a is total, otherwise NONE *)
    val totalTable : unit Table.Table = Table.new(0)

    fun reset () = Table.clear totalTable
    fun install (cid) = Table.insert totalTable (cid, ())
    fun lookup (cid) = Table.lookup totalTable (cid)
    fun uninstall (cid) = Table.delete totalTable (cid)
  in
    val reset = reset
    val install = install
    val uninstall = (fn cid =>
        case lookup cid
          of NONE => false
           | SOME _ => (uninstall cid ; true))

    fun total (cid) = (* call only on constants *)
        case lookup cid
          of NONE => false
           | SOME _ => true

    exception Error' of P.occ * string

    (* copied from terminates/reduces.fun *)
    fun error (c, occ, msg) =
        (case Origins.originLookup c
           of (fileName, NONE) => raise Error (fileName ^ ":" ^ msg)
            | (fileName, SOME occDec) =>
                raise Error (P.wrapLoc' (P.Loc (fileName, P.occToRegionDec occDec occ),
                                        Origins.linesInfoLookup (fileName),
                                        msg)))

    (* G is unused here *)
    fun checkDynOrder (G, Vs, 0, occ) =
        (* raise Error' (occ, "Output coverage for clauses of order >= 3 not yet implemented") *)
        (* Functional calculus now checks this *)
        (* Sun Jan  5 12:17:06 2003 -fp *)
        (if !Global.chatter >= 5
           then print ("Output coverage: skipping redundant checking of third-order clause\n")
         else ();
         ())
      | checkDynOrder (G, Vs, n, occ) = (* n > 0 *)
          checkDynOrderW (G, Whnf.whnf Vs, n, occ)
    and checkDynOrderW (G, (I.Root _, s), n, occ) = ()
        (* atomic subgoal *)
      | checkDynOrderW (G, (I.Pi ((D1 as I.Dec (_, V1), I.No), V2), s), n, occ) =
        (* dynamic (= non-dependent) assumption --- calculate dynamic order of V1 *)
          ( checkDynOrder (G, (V1, s), n-1, P.label occ) ;
            checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ) )
      | checkDynOrderW (G, (I.Pi ((D1, I.Maybe), V2), s), n, occ) =
        (* static (= dependent) assumption --- consider only body *)
          checkDynOrder (I.Decl (G, D1), (V2, I.dot1 s), n, P.body occ)

    (* checkClause (G, (V, s), occ) = ()
       checkGoal (G, (V, s), occ) = ()
       iff local output coverage for V is satisfied
           for clause V[s] or goal V[s], respectively.
       Effect: raises Error' (occ, msg) if coverage is not satisfied at occ.

       Invariants: G |- V[s] : type
    *)
    fun checkClause (G, Vs, occ) = checkClauseW (G, Whnf.whnf Vs, occ)
    and checkClauseW (G, (I.Pi ((D1, I.Maybe), V2), s), occ) =
        (* quantifier *)
        let
          val D1' = N.decEName (G, I.decSub (D1, s))
        in
          checkClause (I.Decl (G, D1'), (V2, I.dot1 s), P.body occ)
        end
      | checkClauseW (G, (I.Pi ((D1 as I.Dec (_, V1), I.No), V2), s), occ) =
        (* subgoal *)
        let
          val _ = checkClause (I.Decl (G, D1), (V2, I.dot1 s), P.body occ)
        in
          checkGoal (G, (V1, s), P.label occ)
        end
      | checkClauseW (G, (I.Root _, s), occ) =
        (* clause head *)
        ()

    and checkGoal (G, Vs, occ) = checkGoalW (G, Whnf.whnf Vs, occ)
    and checkGoalW (G, (V, s), occ) =
        let
          val a = I.targetFam V
          val _ = if not (total a)
                    then raise Error' (occ, "Subgoal " ^ N.qidToString (N.constQid a)
                                       ^ " not declared to be total")
                  else ()
          val _ = checkDynOrderW (G, (V, s), 2, occ)
                 (* can raise Cover.Error for third-order clauses *)
        in
          Cover.checkOut (G, (V, s))
          handle Cover.Error (msg)
          => raise Error' (occ, "Totality: Output of subgoal not covered\n" ^ msg)
        end

    (* checkDefinite (a, ms) = ()
       iff every mode in mode spine ms is either input or output
       Effect: raises Error (msg) otherwise
    *)
    fun checkDefinite (a, M.Mnil) = ()
      | checkDefinite (a, M.Mapp (M.Marg (M.Plus, _), ms')) = checkDefinite (a, ms')
      | checkDefinite (a, M.Mapp (M.Marg (M.Minus, _), ms')) = checkDefinite (a, ms')
      | checkDefinite (a, M.Mapp (M.Marg (M.Star, xOpt), ms')) =
        (* Note: filename and location are missing in this error message *)
        (* Fri Apr  5 19:25:54 2002 -fp *)
        error (a, P.top,
               "Error: Totality checking " ^ N.qidToString (N.constQid a) ^ ":\n"
               ^ "All argument modes must be input (+) or output (-)"
               ^ (case xOpt of NONE => ""
                     | SOME(x) => " but argument " ^ x ^ " is indefinite (*)"  ))

    (* checkOutCover [c1,...,cn] = ()
       iff local output coverage for every subgoal in ci:Vi is satisfied.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun checkOutCover nil = ()
      | checkOutCover (I.Const(c)::cs) =
        ( if !Global.chatter >= 4
            then print (N.qidToString (N.constQid c) ^ " ")
          else () ;
          if !Global.chatter >= 6
            then print ("\n")
          else () ;
          checkClause (I.Null, (I.constType (c), I.id), P.top)
             handle Error' (occ, msg) => error (c, occ, msg) ;
          checkOutCover cs )
      | checkOutCover (I.Def(d)::cs) =
        ( if !Global.chatter >= 4
            then print (N.qidToString (N.constQid d) ^ " ")
          else () ;
          if !Global.chatter >= 6
            then print ("\n")
          else () ;
          checkClause (I.Null, (I.constType (d), I.id), P.top)
             handle Error' (occ, msg) => error (d, occ, msg) ;
          checkOutCover cs )

    (* checkFam (a) = ()
       iff family a is total in its input arguments.
       This requires termination, input coverage, and local output coverage.
       Currently, there is no global output coverage.
       Effect: raises Error (msg) otherwise, where msg has filename and location.
    *)
    fun checkFam (a) =
        let
          (* Ensuring that there is no bad interaction with type-level definitions *)
          val _ = Cover.checkNoDef (a)  (* a cannot be a type-level definition *)
          val _ = Subordinate.checkNoDef (a) (* a cannot depend on type-level definitions *)
                  handle Subordinate.Error (msg) =>
                            raise Subordinate.Error ("Totality checking " ^
                                                     N.qidToString (N.constQid a)
                                                     ^ ":\n" ^ msg)
          (* Checking termination *)
          val _ = ((Timers.time Timers.terminate Reduces.checkFam) a;
                   if !Global.chatter >= 4
                     then print ("Terminates: " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Reduces.Error (msg) => raise Reduces.Error (msg)

          (* Checking input coverage *)
          (* by termination invariant, there must be consistent mode for a *)
          val SOME(ms) = ModeTable.modeLookup a (* must be defined and well-moded *)
          val _ = checkDefinite (a, ms) (* all arguments must be either input or output *)
          val _ = ((Timers.time Timers.coverage Cover.checkCovers) (a, ms) ;
                   if !Global.chatter >= 4
                     then print ("Covers (input): " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Cover.Error (msg) => raise Cover.Error (msg)

          (* Checking output coverage *)
          val _ = if !Global.chatter >= 4
                    then print ("Output coverage checking family " ^ N.qidToString (N.constQid a)
                                ^ "\n")
                  else ()
          val _ = ModeCheck.checkFreeOut (a, ms) (* all variables in output args must be free *)
          val cs = Index.lookup a
          val _ = ((Timers.time Timers.coverage checkOutCover) (cs);
                   if !Global.chatter = 4
                     then print ("\n")
                   else ();
                   if !Global.chatter >= 4
                     then print ("Covers (output): " ^ N.qidToString (N.constQid a) ^ "\n")
                   else ())
                  handle Cover.Error (msg) => raise Cover.Error (msg)
        in
          ()
        end
  end

end;  (* functor Total *)
