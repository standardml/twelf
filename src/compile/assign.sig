(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)

signature ASSIGN =
sig
  (*! structure IntSyn : INTSYN !*)

  (* exception Assignment of string *)
  (* raises Assignment, instantiates EVars as effect *)
  (* val assign : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> IntSyn.Cnstr list *)

  (* assignable (Us,ps) will check if term U[s] unified with template p[s] *)
  (* returns any residual equations that had to be postpone *)
  (* EVars and AVars in ps are instantiated as an effect *)
  val assignable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> (IntSyn.Cnstr list) option

  (* solveCnstr solves dynamically residuated equations *)
  val solveCnstr : IntSyn.Cnstr list -> bool
 
  (* unifiable solves statically residuated equations *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool 

end; (* signature ASSIGN *)
