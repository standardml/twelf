(* cope with nonstandard old smlnj name of PackWord32Little -jcreed 2006.9.15 *)
structure Flit =
  Flit (structure Global = Global
        structure Word = Word32
        structure Pack = Pack32Little
        structure IntSyn = IntSyn
        structure Whnf = Whnf
        structure Print = Print
	structure Names = Names
	structure Index = Index
	structure Table = IntRedBlackTree)
