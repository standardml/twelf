(* Now in paths.fun *)
(*
structure Paths = Paths ();
*)

structure Origins =
  Origins (structure Global = Global
	   structure Table = StringHashTable
	   (*! structure IntSyn' = IntSyn !*)
	   (*! structure Paths' = Paths !*)
	     );
