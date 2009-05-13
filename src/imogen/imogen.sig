
signature IMOGEN = 
sig

datatype input = ConDec of IntSyn.ConDec

val conDecToExp: IntSyn.ConDec -> IntSyn.Exp

val expToFormula: IntSyn.Exp -> Formula.formula

val solve: PFormula.neg -> ND.nd option

val ndToExp: ND.nd * Formula.formula -> IntSyn.Exp

val doit: input -> unit

end

