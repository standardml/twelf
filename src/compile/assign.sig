(* Assignment *)
(* Author: Larry Greenfield *)
(* Modified: Brigitte Pientka *)

signature ASSIGN =
sig
  (*! structure IntSyn : INTSYN !*)

  (* assignable (Us,ps) assigns the term U[s] to the 
     linear higher-order pattern p[s]; if successfull it
     returns a list of residual equations that have been postponed *)
  (* EVars and AVars in ps are instantiated as an effect *)
  val assignable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> (IntSyn.Cnstr list) option

  (* solveCnstr solves dynamically residuated equations *)
  val solveCnstr : IntSyn.Cnstr list -> bool
 
  (* unifiable solves statically residuated equations *)
  val unifiable : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool 

  (* instance solves statically residuated equations *)
  val instance : IntSyn.dctx * IntSyn.eclo * IntSyn.eclo -> bool 
    
  val firstConstArg : IntSyn.Exp * IntSyn.Sub -> IntSyn.cid option
end; (* signature ASSIGN *)
