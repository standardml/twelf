(* Substitution Trees *)
(* Author: Brigitte Pientka *)

signature SUBTREE =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN     !*)
  (*! structure RBSet : RBSET  !*)

  type nvar = int      (* index for normal variables *)
  type bvar = int      (* index for bound variables *)
  type bdepth = int    (* depth of locally bound variables *)

  (* normal (linear) substitutions *)
(*  type normalSubsts = (IntSyn.Dec IntSyn.Ctx * IntSyn.Exp) RBSet.ordSet *)
  datatype typeLabel = TypeLabel | Body
  type normalSubsts =  (typeLabel * IntSyn.Exp) RBSet.ordSet 
  type querySubsts = (IntSyn.Dec IntSyn.Ctx * (typeLabel * IntSyn.Exp)) RBSet.ordSet 

  datatype CGoal = CGoals of CompSyn.AuxGoal * IntSyn.cid  * CompSyn.Conjunction * int

  (* assignable (linear) subsitutions *)
  datatype AssSub = Assign of IntSyn.Dec IntSyn.Ctx * IntSyn.Exp
  type assSubsts = AssSub RBSet.ordSet  (* key = int = bvar *) 

  datatype Cnstr = Eqn of IntSyn.Dec IntSyn.Ctx * IntSyn.Exp * IntSyn.Exp
      
  datatype Tree = 
    Leaf of normalSubsts *  IntSyn.Dec IntSyn.Ctx * CGoal
  | Node of normalSubsts * Tree RBSet.ordSet

(*  type candidate = assSubsts * normalSubsts * cnstrSubsts * Cnstr * IntSyn.Dec IntSyn.Ctx * CGoal *)

  val indexArray : ((int ref) * (Tree ref)) Array.array

  val sProgReset : unit -> unit
  val sProgInstall : (IntSyn.cid * CompSyn.CompHead * CompSyn.Conjunction) -> unit
  val matchSig : IntSyn.cid * IntSyn.Dec IntSyn.Ctx * IntSyn.eclo * 
    ((CompSyn.Conjunction * IntSyn.Sub) * IntSyn.cid -> unit) -> unit 

(*  val goalToString : string -> IntSyn.Dec IntSyn.Ctx * CompSyn.Goal * IntSyn.Sub -> string *)

end;  (* signature SUBTREE *)

