
signature IMOGEN = 
sig

datatype input = ConDec of IntSyn.ConDec

val conDecToExp: IntSyn.ConDec -> IntSyn.Exp

val expToFormula: IntSyn.Exp -> Formula.formula

val expToPFormula: IntSyn.Exp -> PFormula.neg

val solve: PFormula.neg -> ND.nd option

val ndToExp: ND.nd -> IntSyn.Exp

end

