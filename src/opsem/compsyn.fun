(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)
(* Modified: Frank Pfenning *)

functor CompSyn (structure Global : GLOBAL
                 structure IntSyn' : INTSYN
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn')
  : COMPSYN =
struct

  structure IntSyn = IntSyn'

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.cid * Goal		
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)

  (* Representation invariants for compiled syntax:
     Judgments:
       G |- g goal   g is a valid goal in G
       G |- r resgoal  g is a valid residual goal in G

       G |- A ~> g   A compiles to goal g
       G |- A ~> r   A compiles to residual goal r

     G |- p  goal
     if  G |- p : type, p = H @ S	(* mod whnf *)

     G |- (r, A, a) => g  goal
     if G |- A : type
        G |- r  resgoal
	G |- A ~> r
        a  target head of A (for indexing purposes)

     G |- all x:A. g  goal
     if G |- A : type
        G, x:A |- g  goal

     G |- q  resgoal
     if G |- q : type, q = H @ S	(* mod whnf *)

     G |- r & (A,g)  resgoal
     if G |- A : type
        G |- g  goal
        G |- A ~> g
        G, _:A |- r  resgoal

     G |- exists x:A. r  resgoal
     if  G |- A : type
         G, x:A |- r  resgoal
  *)

  (* The dynamic clause pool --- compiled version of the context *)
  type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx

  (* Dynamic programs: context with synchronous clause pool *)
  type dprog = IntSyn.dctx * dpool

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of ResGoal	                (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  local
    val maxCid = Global.maxCid
    val sProgArray = Array.array (maxCid+1, Void) : ConDec Array.array
  in
    (* Invariants *)
    (* 0 <= cid < I.sgnSize () *)

    fun sProgInstall (cid, conDec) = Array.update (sProgArray, cid, conDec)
    fun sProgLookup (cid) = Array.sub (sProgArray, cid)
    fun sProgReset () = Array.modify (fn _ => Void) sProgArray
  end

  (* goalSub (g, s) = g'

     Invariants:
     If   G  |- s : G'    G' |- g : A
     then g' = g[s]
     and  G  |- g' : A
  *)
  fun goalSub (Atom(p), s) = Atom(IntSyn.EClo(p,s))
    | goalSub (Impl(d, A, a, g), s) =
       Impl (resGoalSub (d, s), IntSyn.EClo(A, s), a,
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
    | resGoalSub (Exists(D, r), s) =
       Exists (IntSyn.decSub(D, s), resGoalSub (r, IntSyn.dot1 s))

end;  (* functor CompSyn *)
