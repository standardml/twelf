
signature FRAME =
sig

type frame

val fromDec: IntSyn.cid -> frame

val pp: frame -> PP.pp
val fill: frame -> bool
val split: frame * Var.t -> frame list

end
