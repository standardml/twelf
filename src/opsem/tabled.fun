(* Abstract Machine for tabling*)
(* Author: Brigitte Pientka *)
(* Based on abstract machine in absmachine.fun *)

functor Tabled ((*! structure IntSyn' : INTSYN !*)
                (*! structure CompSyn' : COMPSYN !*)
                (*! sharing CompSyn'.IntSyn = IntSyn' !*)
                structure Unify : UNIFY
                (*! sharing Unify.IntSyn = IntSyn' !*)
                structure TabledSyn : TABLEDSYN
                (*!  sharing TabledSyn.IntSyn = IntSyn' !*)
                structure Assign : ASSIGN
                (*!  sharing Assign.IntSyn = IntSyn' !*)
                structure Index : INDEX
                (*!  sharing Index.IntSyn = IntSyn' !*)
                structure Queue : QUEUE
                (*! structure TableParam : TABLEPARAM !*)
                (*!  sharing TableParam.IntSyn = IntSyn' !*)
                (*!  sharing TableParam.CompSyn = CompSyn' !*)

                structure AbstractTabled : ABSTRACTTABLED
                (*!  sharing AbstractTabled.IntSyn = IntSyn' !*)
                (*! sharing AbstractTabled.TableParam = TableParam !*)
                structure MemoTable : MEMOTABLE
                (*!  sharing MemoTable.IntSyn = IntSyn' !*)
                (*!  sharing MemoTable.CompSyn = CompSyn'  !*)
                (*! sharing MemoTable.TableParam = TableParam  !*)
                (* CPrint currently unused *)
                structure CPrint : CPRINT
                (*!  sharing CPrint.IntSyn = IntSyn' !*)
                (*!  sharing CPrint.CompSyn = CompSyn' !*)
                (* CPrint currently unused *)
                structure Print : PRINT
                (*!  sharing Print.IntSyn = IntSyn' !*)

(*              structure Names : NAMES *)
                (*!  sharing Names.IntSyn = IntSyn' !*)
                (*! structure CSManager : CS_MANAGER !*)
                (*!  sharing CSManager.IntSyn = IntSyn'!*))
  : TABLED =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  structure Unify = Unify
  structure TabledSyn = TabledSyn
  (*! structure TableParam = TableParam !*)
(*  structure Match = Match*)

  local
    structure I = IntSyn
    structure C = CompSyn
    structure A = AbstractTabled
    structure T = TableParam
    structure MT = MemoTable
  in

    (* ---------------------------------------------------------------------- *)
    (* Suspended goal: SuspType, s, G, sc, ftrail, answerRef, i

       where
       s is a substitution for the existential variables in D such that G |- s : G, D
       sc        : is the success continuation
       ftrail    : is a forward trail
       answerRef : pointer to potential answers in the memo-table
       i         : Number of answer which already have been consumed  by this
                   current program state

    *)
    datatype SuspType = Loop | Divergence of ((IntSyn.Exp * IntSyn.Sub) * CompSyn.DProg)

    val SuspGoals : ((SuspType * (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) *  (CompSyn.pskeleton -> unit) *
                      Unify.unifTrail * ((IntSyn.Sub * IntSyn.Sub) * T.answer) * int ref)  list) ref  = ref []

    exception Error of string

  (* ---------------------------------------------------------------------- *)

   fun cidFromHead (I.Const a) = a
     | cidFromHead (I.Def a) = a

   fun eqHead (I.Const a, I.Const a') = a = a'
     | eqHead (I.Def a, I.Def a') = a = a'
     | eqHead _ = false

   fun append(IntSyn.Null, G) = G
     | append(IntSyn.Decl(G', D), G) = IntSyn.Decl(append(G', G), D)

   fun shift (IntSyn.Null, s) = s
     | shift (IntSyn.Decl(G, D), s) = I.dot1 (shift(G, s))

    fun raiseType (I.Null, V) = V
      | raiseType (I.Decl (G, D), V) = raiseType (G, I.Lam (D, V))

    fun compose(IntSyn.Null, G) = G
      | compose(IntSyn.Decl(G, D), G') = IntSyn.Decl(compose(G, G'), D)

    (* ---------------------------------------------------------------------- *)
    (* We write
       G |- M : g
     if M is a canonical proof term for goal g which could be found
     following the operational semantics.  In general, the
     success continuation sc may be applied to such M's in the order
     they are found.  Backtracking is modeled by the return of
     the success continuation.

     Similarly, we write
       G |- S : r
     if S is a canonical proof spine for residual goal r which could
     be found following the operational semantics.  A success continuation
     sc may be applies to such S's in the order they are found and
     return to indicate backtracking.
    *)

    (* ---------------------------------------------------------------------- *)
    (* ctxToEVarSub D = s

     if D is a context for existential variables,
        s.t. u_1:: A_1,.... u_n:: A_n = D
     then . |- s : D where s = X_n....X_1.id

    *)

    fun ctxToEVarSub (I.Null, s) = s
      | ctxToEVarSub (I.Decl(G,I.Dec(_,A)), s) =
      let
        val X = I.newEVar (I.Null, A)
      in
        I.Dot(I.Exp(X), ctxToEVarSub (G, s))
      end

    fun ctxToAVarSub (I.Null, s) = s
      | ctxToAVarSub (I.Decl(G,I.Dec(_,A)), s) =
      let
        val X = I.newEVar (I.Null, A)
      in
        I.Dot(I.Exp(X), ctxToAVarSub (G, s))
      end

      | ctxToAVarSub (I.Decl(G,I.ADec(_,d)), s) =
      let
        val X = I.newAVar ()
      in
        I.Dot(I.Exp(I.EClo(X, I.Shift(~d))), ctxToAVarSub (G, s))
      end


 (* ---------------------------------------------------------------------- *)
 (* Solving  variable definitions *)
 (* solveEqn ((VarDef, s), G) = bool

    if G'' |- VarDef and G  . |- s : G''
       G   |- VarDef[s]
    then
       return true, if VarDefs are solvable
              false otherwise
 *)
  fun solveEqn ((T.Trivial, s), G) = true
    | solveEqn ((T.Unify(G',e1, N, eqns), s), G) =
      (* D, G, G' |- e1 and D, G, G' |- N and D, G |- eqns *)
      (* . |- s : D *)
      let
        val G'' = append (G', G)
        val s' = shift (G'', s)  (* G, G' |- s' : D, G, G' *)
      in
        Assign.unifiable (G'', (N, s'), (e1, s'))
        andalso solveEqn ((eqns, s), G)
     end

  fun unifySub' (G, s1, s2) =
    (Unify.unifySub (G, s1, s2); true)
    handle Unify.Unify msg => false

  fun unify (G, Us, Us') =
    (Unify.unify (G, Us, Us') ; true)
    handle Unify.Unify msg => false


  fun getHypGoal (DProg, (C.Atom p, s)) = (DProg, (p,s))
    | getHypGoal (C.DProg(G, dPool), (C.Impl(r, A, Ha, g), s)) =
    let
      val D' = IntSyn.Dec(NONE, I.EClo(A,s))
    in
      if (!TableParam.strengthen)
        then
          (case MT.memberCtx ((G,I.EClo(A,s)), G) of
             SOME(_) =>
               (let
                  val C.Atom(p) = g   (* is g always atomic? *)
                  val X = I.newEVar(G, I.EClo(A, s))
                in
                  getHypGoal (C.DProg(G,dPool), (g, I.Dot(I.Exp(X),s)))
                end)
           | NONE => getHypGoal (C.DProg(I.Decl(G, D'), I.Decl(dPool, C.Dec(r, s, Ha))), (g, I.dot1 s)))
         else
           getHypGoal (C.DProg(I.Decl(G, D'),I.Decl (dPool, C.Dec(r, s, Ha))), (g, I.dot1 s))
       end
     | getHypGoal (C.DProg(G, dPool), (C.All(D, g), s)) =
       let
         val D' = I.decSub (D, s)
       in
         getHypGoal (C.DProg(I.Decl(G, D'), I.Decl(dPool, C.Parameter)), (g, I.dot1 s))
       end

  fun updateGlobalTable (goal, flag) =
    let
      val (dProg as C.DProg(G, dPool), (p,s)) = getHypGoal (C.DProg(I.Null,I.Null), (goal, I.id))
      val (G', DAVars, DEVars, U', eqn', s') =  A.abstractEVarCtx (dProg, p, s)
      val _ = if solveEqn ((eqn', s'), G')
                     then ()
                   else print "\nresidual equation not solvable!\n"
      val status = if flag then TableParam.Complete else TableParam.Incomplete
    in
      if TabledSyn.keepTable (IntSyn.targetFam U')
        then
          case MT.callCheck (DAVars, DEVars, G', U', eqn', status)
            of T.RepeatedEntry(_, answRef, _) =>
              (TableParam.globalTable := ((DAVars, DEVars, G', U', eqn', answRef, status)::(!TableParam.globalTable)))
          | _ => raise Error "Top level goal should always in the table\n"
      else
        ()
    end



  fun keepTable c = TabledSyn.keepTable c

  fun fillTable () =
    let
      fun insert (nil) = ()
        | insert ((DAVars, DEVars, G', U', eqn', answRef, status)::T) =
        case MT.insertIntoTree (DAVars, DEVars, G', U', eqn', answRef, status)
          of T.NewEntry(_) => insert T
            | _ => ()
    in
      insert (!TableParam.globalTable)
    end


 (*------------------------------------------------------------------------------------------*)
  (* retrieve' ((G, U, s), asub, AnswerList, sc) = ()

     retrieval for subsumption must take into account the asub substitution

     Invariants:
     if
       Goal:                        Answer substitution from index:
       D   |- Pi G. U
       .   |- s : D        and      D' |- s1 : D1
       D   |- asub : D1    and      .  |- s1' : D' (reinstantiate evars)

                                scomp = s1 o s1'
                                  .  |- scomp : D1

       .  |- [esub]asub : D1  where
       .  |- esub : D      and  G |- esub^|G| : D , G
       .  |- s : D         and  G |- s^|G| : D, G
     then
       unify (G, esub^|G|, s^|G|) and unify (G, ([esub]asub)^|G|, scomp^|G|)
       if unification succeeds
         then we continue solving the success continuation.
         otherwise we fail

     Effects: instantiation of EVars in s, s1' and esub
     any effect  sc O1  might have

   *)
   fun retrieve' ((G, U, s), asub, [], sc)  = ()
     | retrieve' ((G, U, s), (esub, asub), (((D', s1), O1)::A), sc) =
     let
       val s1' = ctxToEVarSub (D', I.Shift(I.ctxLength(D')) (* I.id *))
       val scomp =  I.comp(s1, s1')
       val ss = shift (G, s)
       val ss1 = shift (G, scomp)
       val a = I.comp(asub, s)
       val ass = shift (G, a)
       val easub = I.comp(asub,esub)
     in
       CSManager.trail (fn () => if (unifySub'(G, shift(G, esub), ss) andalso
                                     unifySub' (G, shift(G, I.comp(asub, esub)), ss1))
                                   then
                                     (sc O1) (* Succeed *)
                                 else
                                   ());  (* Fail *)
       retrieve' ((G, U, s), (esub,asub), A, sc)
     end


   (* currently not used -- however, it may be better to not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)
   (* retrieveV ((G, U, s), answerList, sc)
      if
        . |- [s]Pi G.U
        . |- s : DAVars, DEVars

        ((DEVars_i, s_i), O_i) is an element in answer list
         DEVars_i |- s_i : DAVars, DEVars
         and O_i is a proof skeleton
      then
        sc O_i is evaluated
        Effects: instantiation of EVars in s

   *)
   fun retrieveV ((G, U, s),  [], sc)  = ()
     | retrieveV ((G, U, s),  (((DEVars, s1), O1)::A), sc) =
     let
       val s1' = ctxToEVarSub (DEVars, I.Shift(I.ctxLength(DEVars)) (* I.id *))
       val scomp =  I.comp(s1, s1')
       val ss = shift (G, s)
       val ss1 = shift (G, scomp)
     (* for subsumption we must combine it with asumb!!! *)
     in
       CSManager.trail (fn () => if unifySub' (G, ss, ss1)
                                   then (sc O1)
                                 else ());
       retrieveV ((G, U, s),  A, sc)
     end

   fun retrieveSW ((G, U, s), asub, AnswL, sc) = retrieve' ((G, U, s), asub, AnswL, sc)

   (* currently not used -- however, it may be better to  not use the same retrieval function for
      subsumption and variant retrieval, and we want to revive this function *)

  (* fun retrieveSW ((G, U, s), asub, AnswL, sc) =
     case (!TableParam.strategy) of
       TableParam.Variant =>  retrieveV ((G, U, s), AnswL, sc)
     | TableParam.Subsumption => retrieve' ((G, U, s), asub, AnswL, sc) *)

   (* retrieve (k, (G, s), (asub, answRef), sc) = ()
      Invariants:
      If
         G |-   s : G, D   where s contains free existential variables defined in D
         answRef is a pointer to the AnswerList

        G |- asub : D, G  asub is the identity in the variant case
        G |- asub : D, G  asub instantiates existential variables in s.

     then the success continuation sc is triggered.

     Effects: instantiation of EVars in s, and asub
   *)
    fun retrieve (k, (G, U, s), (asub, answRef), sc) =
        let
          val lkp  = T.lookup(answRef)
          val asw' = List.take(rev(T.solutions(answRef)),
                               T.lookup(answRef))
          val answ' = List.drop(asw', !k)
        in
        k := lkp;
        retrieveSW ((G, U, s), asub, answ', sc)
        end

  (* ---------------------------------------------------------------------- *)

   (* solve ((g, s), dp, sc) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- g  goal
     if  G |- M : g[s]
       then  sc M  is evaluated
     Effects: instantiation of EVars in g, s, and dp
     any effect  sc M  might have
     *)
   fun solve ((C.Atom(p), s), dp as C.DProg (G, dPool), sc) =
     if TabledSyn.tabledLookup (I.targetFam p)
       then
         let
           val (G', DAVars, DEVars, U', eqn', s') =  A.abstractEVarCtx (dp, p, s)
           (* Invariant about abstraction:
              Pi DAVars. Pi DEVars. Pi G'. U'    : abstracted linearized goal
              .  |- s' : DAVars, DEVars             k = |G'|
              G' |- s'^k : DAVars, DEVars, G'
               . |- [s'](Pi G'. U')     and  G |- [s'^k]U' = [s]p *)

           val _ = if solveEqn ((eqn', s'), G')
                     then ()
                   else print "\nresidual equation not solvable! -- This should never happen! \n"
         in

           case MT.callCheck (DAVars, DEVars, G', U', eqn', T.Incomplete)
             (* Side effect: D', G' |- U' added to table *)
             of T.NewEntry (answRef) =>
                 matchAtom ((p,s), dp,
                          (fn pskeleton =>
                           case MT.answerCheck (s', answRef, pskeleton) of
                             T.repeated => ()
                           | T.new      => (sc pskeleton)))

           | T.RepeatedEntry(asub,answRef, T.Incomplete) =>
               if T.noAnswers answRef then
                 (* loop detected
                  * NOTE: we might suspend goals more than once.
                  *     example: answer list for goal (p,s) is saturated
                  *              but not the whole table is saturated.
                  *)
                 (SuspGoals :=  ((Loop, (G', U', s'), sc, Unify.suspend(),
                                  (asub, answRef), ref 0)::(!SuspGoals));
                  ())
               else
                 (* loop detected
                  * new answers available from previous stages
                  * resolve current goal with all possible answers
                  *)
                 let
                   val le = T.lookup(answRef)
                 in
                   SuspGoals := ((Loop, (G', U', s'), sc, Unify.suspend(),
                                  (asub, answRef), ref le)::(!SuspGoals));
                   retrieve (ref 0,  (G', U', s'), (asub, answRef), sc)
                 end

           | T.RepeatedEntry(asub, answRef, T.Complete) =>
               if T.noAnswers answRef then
                 (* Subgoal is not provable *)
                  ()
               else
                 (* Subgoal is provable - loop detected
                  * all answers are available from previous run
                  * resolve current goal with all possible answers
                  *)
                   retrieve (ref 0,  (G', U', s'), (asub, answRef), sc)

           | T.DivergingEntry(asub, answRef) =>
                 (* loop detected  -- currently not functioning correctly.
                    we might be using this as part of a debugger which suggests diverging goals
                    to the user so the user can prove a generalized goal first.
                    Wed Dec 22 08:27:24 2004 -bp
                  *)
                 (SuspGoals :=  ((Divergence ((p,s), dp), (G', U', s'), sc, Unify.suspend() ,
                                  ((I.id (* this is a hack *), asub), answRef), ref 0)::(!SuspGoals));
                  ())
         end
     else
         matchAtom ((p, s), dp, sc)

     | solve ((C.Impl(r, A, Ha, g), s), C.DProg (G, dPool), sc) =
       let
         val D' = I.Dec(NONE, I.EClo(A,s))
       in
         if (!TableParam.strengthen)
           then
             (case MT.memberCtx ((G,I.EClo(A,s)), G) of
                SOME(_) =>
                  (let
                    val X = I.newEVar(G, I.EClo(A, s))
                  in
                    solve ((g, I.Dot(I.Exp(X),s)), C.DProg (G, dPool), (fn O => sc O))
                  end)
             | NONE => solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                              (fn O => sc O)))
         else
           solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl (dPool, C.Dec(r, s, Ha))),
                  (fn O => sc O))
       end
     | solve ((C.All(D, g), s), C.DProg (G, dPool), sc) =
       let
         val D' = I.decSub (D, s)
       in
         solve ((g, I.dot1 s), C.DProg (I.Decl(G, D'), I.Decl(dPool, C.Parameter)),
                (fn O => sc O))
       end

   (* rsolve ((p,s'), (r,s), dp, sc) = ()
    Invariants:
    dp = (G, dPool) where G ~ dPool
    G |- s : G'
    G' |- r  resgoal
    G |- s' : G''
    G'' |- p : H @ S' (mod whnf)
    if G |- S : r[s]
       then sc S is evaluated
     Effects: instantiation of EVars in p[s'], r[s], and dp
     any effect  sc S  might have
     *)
   and rSolve (ps', (C.Eq(Q), s), C.DProg (G, dPool), sc) =
       (if Unify.unifiable (G, ps', (Q, s)) (* effect: instantiate EVars *)
            then
              sc []                       (* call success continuation *)
          else  ())                       (* fail *)

        | rSolve (ps', (C.Assign(Q, eqns), s), dp as C.DProg(G, dPool), sc) =
       (case Assign.assignable (G, ps', (Q, s)) of
          SOME(cnstr) =>
            aSolve((eqns, s), dp, cnstr, (fn S => sc S))
        | NONE => ())

     | rSolve (ps', (C.And(r, A, g), s), dp as C.DProg (G, dPool), sc) =
       let
        (* is this EVar redundant? -fp *)
        val X = I.newEVar(G, I.EClo(A, s))
      in
        rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp,
                (fn S1 => solve ((g, s), dp, (fn S2 => sc (S1@S2)))))
      end
     | rSolve (ps', (C.Exists(I.Dec(_,A), r), s), dp as C.DProg (G, dPool), sc) =
       let
         val X = I.newEVar(G, I.EClo(A, s))
       in
         rSolve (ps', (r, I.Dot(I.Exp(X), s)), dp, (fn S => sc S))
       end

     | rSolve (ps', (C.Axists(I.ADec(SOME(X), d), r), s), dp as C.DProg (G, dPool), sc) =
       let
         val X' = I.newAVar ()
       in
         rSolve (ps', (r, I.Dot(I.Exp(I.EClo(X', I.Shift(~d))), s)), dp, sc)
         (* we don't increase the proof term here! *)
       end


  (* aSolve ((ag, s), dp, sc) = res
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       if G |- ag[s] auxgoal
       then sc () is evaluated with return value res
       else res = Fail
     Effects: instantiation of EVars in ag[s], dp and sc () *)

  and aSolve ((C.Trivial, s), dp, cnstr, sc) =
        (if Assign.solveCnstr cnstr  then
          (sc [])
        else
           ())
    | aSolve ((C.UnifyEq(G',e1, N, eqns), s), dp as C.DProg(G, dPool), cnstr, sc) =
      let
        val (G'') = append(G', G)
        val s' = shift (G', s)
      in
        if Assign.unifiable (G'', (N, s'), (e1, s')) then
              aSolve ((eqns, s), dp, cnstr, sc)
        else ()
     end

  (* matchatom ((p, s), dp, sc) => ()
     Invariants:
       dp = (G, dPool) where G ~ dPool
       G |- s : G'
       G' |- p : type, p = H @ S mod whnf
       if G |- M :: p[s]
       then sc M is evaluated
     Effects: instantiation of EVars in p[s] and dp
              any effect  sc M  might have

     This first tries the local assumptions in dp then
     the static signature.
  *)
  and matchAtom (ps' as (I.Root(Ha,S),s), dp as C.DProg (G,dPool), sc) =
      let
        (* matchSig [c1,...,cn] = ()
           try each constant ci in turn for solving atomic goal ps', starting
           with c1.
        *)
        fun matchSig nil = ()   (* return indicates failure *)
          | matchSig ((Hc as I.Const c)::sgn') =
            let
              val C.SClause(r) = C.sProgLookup (cidFromHead Hc)
            in
              (* trail to undo EVar instantiations *)
              CSManager.trail (fn () =>
                               rSolve (ps', (r, I.id), dp,
                                          (fn S =>
                                             sc ((C.Pc c)::S) )));
              matchSig sgn'
            end

        (* matchDProg (dPool, k) = ()
           where k is the index of dPool in global dPool from call to matchAtom.
           Try each local assumption for solving atomic goal ps', starting
           with the most recent one.
        *)
        fun matchDProg (I.Null, I.Null, _) =
            (* dynamic program exhausted, try signature *)
            matchSig (Index.lookup (cidFromHead Ha))

          | matchDProg (I.Decl(G, _),
                        I.Decl (dPool', C.Dec(r, s, Ha')), k) =
            if eqHead (Ha, Ha')
              then
                (* trail to undo EVar instantiations *)
                (CSManager.trail (fn () =>
                                    rSolve (ps', (r, I.comp(s, I.Shift(k))), dp,
                                            (fn S => sc ((C.Dc k)::S))));
                   matchDProg (G, dPool', k+1))

            else matchDProg (G, dPool', k+1)
          | matchDProg (I.Decl(G, _), I.Decl (dPool', C.Parameter), k) =
              matchDProg (G, dPool', k+1)

          fun matchConstraint (solve, try) =
            let
              val succeeded =
                CSManager.trail
                (fn () =>
                 case (solve (G, I.SClo (S, s), try))
                   of SOME(U) => (sc [C.Csolver U]; true)
                 | NONE => false)
            in
              if succeeded
                then matchConstraint (solve, try+1)
              else ()
            end
      in
        case I.constStatus(cidFromHead Ha)
          of (I.Constraint (cs, solve)) => matchConstraint (solve, 0)
        | _ => matchDProg (G, dPool, 1)
      end

  (* retrieval ((p, s), dp, sc, answRef, n) => ()
     Invariants:
     dp = (G, dPool) where  G ~ dPool  (context G matches dPool)
     G |- s : G'
     G' |- p  goal
     answRef : pointer to corresponding answer list
     n       : #number of answers which were already consumed
               by the current goal

     if answers are available
      then retrieve all new answers
     else fail
     *)
  fun retrieval (Loop, (G', U', s'), sc, (asub, answRef), n) =
    if T.noAnswers answRef then
      (* still  no answers available from previous stages *)
      (* NOTE: do not add the susp goal to suspGoal list
                because it is already in the suspGoal list *)
      ()
    else
      (*  new answers available from previous stages
       * resolve current goal with all "new" possible answers
       *)
      retrieve (n, (G', U', s'), (asub, answRef), sc)

    | retrieval (Divergence ((p,s), dp), (G', U', s'), sc, (asub, answRef), n) =
      matchAtom ((p, s), dp,
             (fn pskeleton =>
              case MT.answerCheck (s', answRef, pskeleton)
                of T.repeated => ()
              | T.new      => sc pskeleton))



  fun tableSize () =  MT.tableSize ()
  fun suspGoalNo () =  List.length(!SuspGoals)

  (*  nextStage () = bool
     Side effect: advances lookup pointers
   *)

  fun nextStage () =
    let
      fun resume [] = ()
        | resume (((Susp, s, sc, trail, (asub, answRef), k)::Goals)) =
        (CSManager.trail        (fn () => (Unify.resume trail;
                                           retrieval (Susp, s, sc, (asub, answRef), k)));
         resume (Goals))
      val SG = rev(!SuspGoals)
    in
      if MT.updateTable () then
        (* table changed during previous stage *)
        (TableParam.stageCtr := (!TableParam.stageCtr) + 1;
         resume (SG);
         true)
      else
        (* table did not change during previous stage *)
        false
   end


 fun reset () = (SuspGoals := []; MT.reset(); TableParam.stageCtr := 0)

 fun solveQuery ((g, s), dp as C.DProg (G, dPool), sc) =
   (* only works when query is atomic -- if query is not atomic,
      then the subordination relation might be extended and strengthening may not be sound *)
   solve((g, s), dp, sc)

  end (* local ... *)

 val solve = solveQuery

end; (* functor Tabled *)



