(* Compiled Syntax *)
(* Author: Iliano Cervesato *)
(* Modified: Jeff Polakow *)

signature COMPSYN =
sig

  structure IntSyn : INTSYN

  datatype Goal =                       (* Goals                      *)
    Atom of IntSyn.Exp                  (* g ::= p                    *)
  | Impl of ResGoal * IntSyn.Exp        (*     | (r,A,a) => g         *)
            * IntSyn.cid * Goal		
  | All  of IntSyn.Dec * Goal           (*     | all x:A. g           *)

  and ResGoal =                         (* Residual Goals             *)
    Eq     of IntSyn.Exp                (* r ::= p = ?                *)
  | Assign of IntSyn.Exp * AuxGoal      (* r ::= p = ?, where p has   *)
					(* only new vars,             *)  
                                        (* then unify all the vars    *)
  | And    of ResGoal                   (*     | r & (A,g)            *)
              * IntSyn.Exp * Goal       
  | Meta   of ResGoal			(*     | r && (A,g)    x      *)
              * IntSyn.Exp * Goal       
  | Exists of IntSyn.Dec * ResGoal      (*     | exists x:A. r        *)
  | Exists' of IntSyn.Dec * ResGoal	(*     | exists x:A. r        *)

  and AuxGoal =
    Trivial				(* trivially done *)
  | Unify of IntSyn.Eqn * AuxGoal	(* call unify on IntSyn.eqn *)

  (* The dynamic clause pool --- compiled version of the context *)
  (* type dpool = (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx *)

  (* Dynamic programs: context with synchronous clause pool *)
  datatype DProg = DProg of (IntSyn.dctx * (ResGoal * IntSyn.Sub * IntSyn.cid) option IntSyn.Ctx)

  (* Static programs --- compiled version of the signature *)
  datatype ConDec =			(* Compiled constant declaration *)
    SClause of ResGoal	                (* c : A                      *)
  | Void 		                (* Other declarations are ignored  *)

  val sProgInstall : IntSyn.cid * ConDec -> unit
  val sProgLookup: IntSyn.cid -> ConDec
  val sProgReset : unit -> unit

  (* Explicit Substitutions *)
  val goalSub   : Goal * IntSyn.Sub -> Goal
  val resGoalSub: ResGoal * IntSyn.Sub -> ResGoal

end;  (* signature COMPSYN *)
