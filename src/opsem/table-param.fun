(* Table parameters *)
(* Author: Brigitte Pientka *)

functor TableParam (structure Global : GLOBAL
                    (*! structure IntSyn' : INTSYN !*)
                    (*! structure CompSyn' : COMPSYN !*)
                    (*!  sharing CompSyn'.IntSyn = IntSyn'!*)
                    (*! structure RBSet : RBSET!*))
: TABLEPARAM =
struct

  (*! structure IntSyn = IntSyn' !*)
  (*! structure CompSyn = CompSyn' !*)
  (*! structure RBSet = RBSet !*)

   exception Error of string

   datatype Strategy = Variant | Subsumption

   datatype ResEqn =
     Trivial                              (* trivially done *)
   | Unify of IntSyn.dctx * IntSyn.Exp    (* call unify *)
     * IntSyn.Exp * ResEqn

   type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub)
                               * CompSyn.pskeleton) list,
                  lookup: int} ref

   datatype Status = Complete | Incomplete

   (* globalTable stores the queries whose solution we want to keep *)
   val globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx *
                       IntSyn.Exp * ResEqn * answer * Status ) list ref
                      = ref []

   fun resetGlobalTable () = (globalTable := [])

   fun emptyAnsw () = ref {solutions = [], lookup = 0}

   fun addSolution (S, answRef) =
     let
       val {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = (S::SList), lookup = k}
     end

   fun updateAnswLookup (k',answRef) =
     let
       val {solutions = SList, lookup = k} = !answRef
     in
       answRef := {solutions = SList, lookup = k'}
     end

   fun solutions (answ as ref {solutions = S, lookup = i}) = S
   fun lookup (answ as ref {solutions = S, lookup = i}) = i

   fun noAnswers answ =
     (case (List.take (solutions(answ), lookup(answ))) (*solutions(answ) *)
        of [] => true
      | L  => false)

   type asub = IntSyn.Exp RBSet.ordSet
   val aid : unit -> asub = RBSet.new


   datatype callCheckResult =
       NewEntry of answer
     | RepeatedEntry of (IntSyn.Sub * IntSyn.Sub) * answer * Status
     | DivergingEntry of (IntSyn.Sub * answer)

   datatype answState = new | repeated

(* ---------------------------------------------------------------------- *)
(* global search parameters *)

  val strategy  = ref Variant (* Subsumption *)

  val divHeuristic = ref false;
(*  val divHeuristic = ref true;*)

  val stageCtr = ref 0;

 (* term abstraction and ctx abstraction *)
 (* currently not used *)
  val termDepth = ref NONE : int option ref;
  val ctxDepth = ref NONE : int option ref;
  val ctxLength = ref NONE : int option ref;

  (* apply strengthening during abstraction *)
  val strengthen = ref false ;


end;  (* structure TableParam *)

