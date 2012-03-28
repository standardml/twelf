(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)
(* Modified: Brigitte Pientka *)

functor CompSyn (structure Global : GLOBAL
                 (*! structure IntSyn' : INTSYN !*)
                 structure Names : NAMES
                 (*! sharing Names.IntSyn = IntSyn' !*)
                 structure Table : TABLE
                   where type key = int)
  : COMPSYN =
struct

  (*! structure IntSyn = IntSyn' !*)


  datatype Opt = No | LinearHeads | Indexing

  val optimize = ref LinearHeads

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.Head * Goal
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | Assign of IntSyn.Exp * AuxGoal      (*     | p = ?, where p has   *)
                                        (* only new vars,             *)
                                        (* then unify all the vars    *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal
  | In     of ResGoal                   (*     | r && (A,g)           *)
              * IntSyn.Exp * Goal
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)
  | Axists of IntSyn.Dec * ResGoal      (*     | exists' x:_. r       *)
                                        (* exists' is used for local evars
                                           which are introduced to linearize
                                           the head of a clause;
                                           they do not have a type -bp *)

  and AuxGoal =
    Trivial                               (* trivially done *)
  | UnifyEq of IntSyn.dctx * IntSyn.Exp   (* call unify *)
             * IntSyn.Exp * AuxGoal

  (* Static programs -- compiled version for substitution trees *)
  datatype Conjunction = True | Conjunct of Goal * IntSyn.Exp * Conjunction

  datatype CompHead =
     Head of (IntSyn.Exp * IntSyn.Dec IntSyn.Ctx * AuxGoal * IntSyn.cid)


  (* proof skeletons instead of proof term *)
  datatype Flatterm =
    Pc of IntSyn.cid | Dc of IntSyn.cid | Csolver of IntSyn.Exp

  type pskeleton = Flatterm list

  (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r
       G |- A ~> <head , subgoals>

     G |- p  goal
     if  G |- p : type, p = H @ S       (* mod whnf *)

     G |- (r, A, a) => g  goal
     if G |- A : type
        G |- r  resgoal
        G |- A ~> r
        a  target head of A (for indexing purposes)

     G |- all x:A. g  goal
     if G |- A : type
        G, x:A |- g  goal

     For dynamic clauses:

     G |- q  resgoal
     if G |- q : type, q = H @ S        (* mod whnf *)

     G |- r & (A,g)  resgoal
     if G |- A : type
        G |- g  goal
        G |- A ~> g
        G, _:A |- r  resgoal

     G |- exists x:A. r  resgoal
     if  G |- A : type
         G, x:A |- r  resgoal

     G |- exists' x:A. r  resgoal     but exists' doesn't effect the proof-term
     if  G |- A : type
         G, x:A |- r  resgoal

     For static clauses:
     G |- true subgoals

     if G |- sg && g subgoals
     if G |- g goal
        G |- sg subgoals

  *)

  (* Static programs --- compiled version of the signature (no indexing) *)
  datatype ConDec =                        (* Compiled constant declaration           *)
       SClause of ResGoal                  (* c : A  -- static clause (residual goal) *)
    | Void                                 (* Other declarations are ignored          *)

  (* Static programs --- compiled version of the signature (indexed by first argument) *)
  datatype ConDecDirect =                  (* Compiled constant declaration     *)
      HeadGoals of CompHead * Conjunction  (* static clause with direct head access   *)
    | Null                                 (* Other declarations are ignored          *)

  (* Compiled Declarations *)
  (* added Thu Jun 13 13:41:32 EDT 2002 -cs *)
  datatype ComDec =
    Parameter
  | Dec of ResGoal * IntSyn.Sub * IntSyn.Head
  | BDec of (ResGoal * IntSyn.Sub *IntSyn.Head) list
  | PDec

  (* The dynamic clause pool --- compiled version of the context *)
  (* Dynamic programs: context with synchronous clause pool *)

  datatype DProg = DProg of IntSyn.dctx * ComDec IntSyn.Ctx

  local
    val maxCid = Global.maxCid
    (* program array indexed by clause names (no direct head access) *)
    val sProgArray = Array.array (maxCid+1, Void) : ConDec Array.array

    val detTable : bool Table.Table = Table.new (32)
  in
    (* Invariants *)
    (* 0 <= cid < I.sgnSize () *)
    (* program array indexed by clause names (no direct head access) *)
    fun sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)

    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgReset () = Array.modify (fn _ => Void) sProgArray

    val detTableInsert = Table.insert detTable;
    fun detTableCheck (cid) = (case (Table.lookup detTable cid)
                                 of SOME(deterministic) => deterministic
                                  | NONE => false)
    fun detTableReset () = Table.clear detTable;
  end
  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  fun goalSub (Atom(p), s) = Atom(IntSyn.EClo(p,s))
    | goalSub (Impl(d, A, Ha, g), s) =
       Impl (resGoalSub (d, s), IntSyn.EClo(A, s), Ha,
             goalSub (g, IntSyn.dot1 s))
    | goalSub (All(D, g), s) =
       All (IntSyn.decSub(D,s), goalSub (g, IntSyn.dot1 s))

  (* resGoalSub (r, s) = r'

     Invariants:
     If   G  |- s : G'    G' |- r : A
     then r' = r[s]
     and  G  |- r' : A [s]
  *)
  and resGoalSub (Eq(q), s) = Eq (IntSyn.EClo (q,s))
    | resGoalSub (And(r, A, g), s) =
        And (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (In(r, A, g), s) =
        In (resGoalSub (r, IntSyn.dot1 s), IntSyn.EClo(A,s), goalSub (g, s))
    | resGoalSub (Exists(D, r), s) =
        Exists (IntSyn.decSub(D, s), resGoalSub (r, IntSyn.dot1 s))


  fun pskeletonToString [] = " "
    | pskeletonToString ((Pc i)::O) =
        Names.qidToString (Names.constQid i) ^ " " ^ (pskeletonToString O)
    | pskeletonToString ((Dc i)::O) =
        ("(Dc " ^ (Int.toString i) ^ ") ") ^ (pskeletonToString O)
    | pskeletonToString (Csolver U ::O) =
        ("(cs _ ) " ^ (pskeletonToString O))


end;  (* functor CompSyn *)

structure CompSyn =
  CompSyn (structure Global = Global
           (*! structure IntSyn' = IntSyn !*)
           structure Names = Names
           structure Table = IntRedBlackTree);

