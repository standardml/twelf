(* Global Table parameters *)
(* Author: Brigitte Pientka *)

signature TABLEPARAM =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
  (*! structure RBSet : RBSET !*)

  exception Error of string

  (* Residual equation *)
  datatype ResEqn =
    Trivial				  (* trivially done *)
  | Unify of IntSyn.dctx * IntSyn.Exp     (* call unify *)
    * IntSyn.Exp * ResEqn

  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list,
		 lookup: int} ref
    
  datatype Status = Complete | Incomplete

  val globalTable : (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * 
		      IntSyn.Exp * ResEqn * answer * Status ) list ref

  val resetGlobalTable : unit -> unit

  val emptyAnsw : unit -> answer

(* destructively updates answers *)
 val addSolution : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) * answer 
                  -> unit

 val updateAnswLookup : int * answer -> unit

 val solutions : answer -> ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list
 val lookup : answer -> int
 val noAnswers : answer -> bool

(* ---------------------------------------------------------------------- *)
 type asub  = IntSyn.Exp RBSet.ordSet 

 val aid : unit -> asub

 datatype callCheckResult = 
    NewEntry of answer 
  | RepeatedEntry of (IntSyn.Sub * IntSyn.Sub) * answer * Status
  | DivergingEntry of IntSyn.Sub * answer

  datatype answState = new | repeated

(* ---------------------------------------------------------------------- *)

  datatype Strategy = Variant | Subsumption


  val strategy  : Strategy ref 
  val stageCtr  : int ref
  val divHeuristic : bool ref;

  val termDepth  : int option ref
  val ctxDepth   : int option ref
  val ctxLength  : int option ref 

  val strengthen : bool ref

end;  (* signature TABLEPARAM *)
