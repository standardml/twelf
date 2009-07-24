
signature TWELF_UTIL =
sig

exception TwelfUtil of string

(* -------------------------------------------------------------------------- *)
(*  Util                                                                      *)
(* -------------------------------------------------------------------------- *)

val decName : IntSyn.cid -> string

(* -------------------------------------------------------------------------- *)
(*  Translations                                                              *)
(* -------------------------------------------------------------------------- *)

(* getCons id
   Get all decs that are constructors of type id.
 *)
val getCons : IntSyn.cid -> IntSyn.ConDec list

(* decToFormula `{X}{Y}{Z} plus X Y Z -> plus X (s Y) (s Z) -> type` --->
                `! [X, Y, Z] : (plus(X, Y, Z) => plus(X, s(Y), s(Z)))`
 *) 
val decToFormula : IntSyn.ConDec -> Formula.formula

(* decToTerm `s X` ---> `s(X)` *) 
val decToTerm : IntSyn.ConDec -> Term.term

(* unifyConcl(`! [X, Y, Z] : (plus(X, Y, Z) => plus(s(X), Y, s(Z)))`, 
              `plus(X', Y', Z')`) ---> 
        SOME ([X' |-> s(X), Y' |-> Y, Z' |-> s(Z)],
              [plus(X, Y, Z), plus(s(X), Y, s(Z))])
*) 
val unifyConcl : Formula.formula * Rel.t -> (Subst.t * Rel.t list) option

(* -------------------------------------------------------------------------- *)
(*  Frames                                                                    *)
(* -------------------------------------------------------------------------- *)

type var = Var.t * IntSyn.cid

val ppVar : var -> PP.pp

type clause = Var.t * Rel.t * IntSyn.cid

val ppClause : clause -> PP.pp

datatype frame = Frame of { univ   : var list
                          , assums : clause list
                          , exis   : var list
                          , goals  : clause list
                          }

val ppFrame : frame -> PP.pp

val decFrame : IntSyn.cid -> frame

end

