structure Whnf =
  Whnf ((*! structure IntSyn' = IntSyn !*));

structure Conv =
  Conv ((*! structure IntSyn' = IntSyn !*)
	structure Whnf = Whnf);

structure Tomega : TOMEGA =
   Tomega ((*! structure IntSyn' = IntSyn !*)
	   structure Whnf = Whnf
	   structure Conv = Conv);
