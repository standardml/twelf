structure Order =
  Order ((*! structure IntSyn' = IntSyn !*)
	 structure Table = CidRedBlackTree);
(* -bp *)
(*
structure RedOrder = 
    RedOrder ((*! structure IntSyn' = IntSyn !*)
	      structure Table = IntRedBlackTree); 
*)