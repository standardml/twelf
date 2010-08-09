signature SORTCHECK =
  sig
    val check : IntSyn.dctx * IntSyn.Exp * IntSyn.Exp -> bool
  end
