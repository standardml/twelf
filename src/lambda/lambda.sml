(* Now in intsyn.fun *)
(*
structure IntSyn =
  IntSyn (structure Global = Global);
*)

structure Whnf =
  Whnf ((*! structure IntSyn' = IntSyn !*));

structure Conv =
  Conv ((*! structure IntSyn' = IntSyn !*)
	structure Whnf = Whnf);

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

structure Abstract =
  Abstract ((*! structure IntSyn' = IntSyn !*)
	    structure Whnf = Whnf
	    structure Constraints = Constraints
	    structure Unify = UnifyNoTrail);

structure Approx =
  Approx ((*! structure IntSyn' = IntSyn !*)
          structure Whnf = Whnf);
