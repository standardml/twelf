(* Now in intsyn.fun *)
(*
structure IntSyn =
  IntSyn (structure Global = Global);
*)

(* Now in tomega.sml *)
(*
structure Whnf =
  Whnf ((*! structure IntSyn' = IntSyn !*));

structure Conv =
  Conv ((*! structure IntSyn' = IntSyn !*)
	structure Whnf = Whnf);

structure Tomega : TOMEGA =
   Tomega (structure IntSyn' = IntSyn
	   structure Whnf = Whnf
	   structure Conv = Conv)
*)

structure Constraints =
  Constraints ((*! structure IntSyn' = IntSyn !*)
	       structure Conv = Conv);

structure UnifyNoTrail =
  Unify ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Trail = NoTrail);

structure UnifyTrail =
  Unify ((*! structure IntSyn' = IntSyn !*)
	 structure Whnf = Whnf
	 structure Trail = Trail);

(* structure Normalize : NORMALIZE =  
  Normalize ((*! structure IntSyn' = IntSyn !*)
             (*! structure Tomega' = Tomega !*)
             structure Whnf = Whnf)
 *)

structure Match = 
  Match (structure Whnf = Whnf
	 structure Unify = UnifyTrail
	 structure Trail = Trail);

structure Abstract =
  Abstract (structure Whnf = Whnf
	    structure Constraints = Constraints
	    structure Unify = UnifyNoTrail);

structure Approx =
  Approx ((*! structure IntSyn' = IntSyn !*)
          structure Whnf = Whnf);
