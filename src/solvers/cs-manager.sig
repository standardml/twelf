(* Constraint Solver Manager *)
(* Author: Roberto Virga *)

signature CS_MANAGER =
sig
  (* structure IntSyn : INTSYN *)
  structure Fixity  : FIXITY
  (*! structure ModeSyn : MODESYN !*)

  type sigEntry = (* global signature entry *)
    (* constant declaration plus optional precedence and mode information *)
    IntSyn.ConDec * Fixity.fixity option * ModeSyn.ModeSpine list

  type fgnConDec = (* foreign constant declaration *)
    {
      parse : string -> IntSyn.ConDec option
    }

  type solver = (* constraint solver *)
    {
      (* name is the name of the solver *)
      name : string,
      (* keywords identifying the type of solver *)
      (* NOTE: no two solvers with the same keywords may be active simultaneously *)
      keywords : string,
      (* names of other constraint solvers needed *)
      needs : string list,
      (* foreign constants declared (if any) *)
      fgnConst : fgnConDec option,
      (* install constants *)
      init : (int * (sigEntry -> IntSyn.cid)) -> unit,
      (* reset internal status *)
      reset : unit -> unit,
      (* trailing operations *)
      mark : unit -> unit,
      unwind : unit -> unit
    }
  
  exception Error of string

  (* solver handling functions *)
  val setInstallFN : (sigEntry -> IntSyn.cid) -> unit

  val installSolver : solver -> IntSyn.csid
  val resetSolvers  : unit -> unit
  val useSolver     : string -> unit

  (* parsing foreign constatnts *)
  val parse : string -> (IntSyn.csid * IntSyn.ConDec) option

  (* trailing operations *)
  val reset : unit -> unit
  val trail  : (unit -> 'a) -> 'a

end  (* signature CS_MANAGER *)