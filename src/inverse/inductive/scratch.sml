
Control.Print.printLength := 1000; 
Control.Print.printDepth := 1000;
Control.Print.stringDepth := 1000;

val home = "/Users/sean/save/versioned/projects/imogen/src/";

CM.make (home ^ "fol/formulas/sources.cm");
CM.make (home ^ "sml-ext/sources.cm");
CM.make (home ^ "twelf/sources.cm");
CM.make (home ^ "/sources.cm");
CM.make (home ^ "/inductive/sources.cm");

OS.FileSys.getDir();
Twelf.make "elf/sources.cfg";

structure T = Term;
structure F = Formula;
structure U = TwelfUtil;
structure S = IntSyn;
structure MS = ModeSyn;
structure MT = ModeTable;
structure M = Frame;
open GeneralExt;




val f = U.getGoal 6
val f = U.getGoal 9
val f = U.getGoal 10
val f = U.getGoal 13
  handle U.TwelfUtil s => raise Fail s

PP.pp(F.pp f)

S.sgnLookup 6
S.sgnLookup 9
S.sgnLookup 10
MT.modeLookup 6
MT.modeLookup 9
MT.modeLookup 10


Print.conDecToString (S.sgnLookup 10)

U.getConForm 0


PP.pp(F.pp (U.getConForm 3))

val 



U.getCons 0
PP.pp(F.pp(U.decToFormula (List.nth(U.getCons 3, 1))))
PP.pp(F.pp(U.decToFormula (List.nth(U.getCons 3, 0))))

val ` = PP.pp o F.pp
val `` = PP.pp o Rel.pp
val ``` = PP.pp o Term.pp
val $ = Parse.parseFormulaStr
val $$ = Parse.parseRel
val $$$ = Parse.parseTerm

val plus0 = U.decToFormula (List.nth(U.getCons 3, 1))
val plusS = U.decToFormula (List.nth(U.getCons 3, 0))

`plus0
`plus1

val plus0 = U.decToFormula (List.nth(U.getCons 0, 0))
val plusS = U.decToFormula (List.nth(U.getCons 0, 1))

U.getCons 0
```(U.decToTerm (List.nth(U.getCons 0, 1)))
```it

`plus0
`plusS

val SOME rels = U.unifyConcl(plusS, $$"plus(X', Y', Z')")
val SOME rels = U.unifyConcl(plus0, $$"plus(X', Y', Z')")
map `` rels
1


S.sgnLookup 0
S.sgnLookup 1
S.sgnLookup 2
S.sgnLookup 3
S.sgnLookup 4
S.sgnLookup 5
S.sgnLookup 6
S.sgnLookup 7
S.sgnLookup 8
S.sgnLookup 9
S.sgnLookup 10
S.sgnLookup 15

S.sgnSize()

U.getMode 6


structure I = FolInstance
structure T = I.Type
structure F = Formula
structure P = Parse

val ` = P.parseFormulaStr
val $ = PFormula.formulate
infixr 9 ==>
val op==> = F.Imp

val (mkGoal : string -> F.formula, addClause : string -> unit) =                
    let
       val cs = ref []
       fun clauses() = F.listConj(!cs)
       fun addClause s = cs := `s :: !cs
       fun mkGoal s = F.Imp(clauses(), `s)
    in
       (mkGoal, addClause)
    end

U.getCons 3

addClause "![X] : p(z, X, X)"
addClause "![X, Y, Z] : (p(X,Y,Z) => p(s(X),Y,s(Z)))"

addClause "![X, Y] : (p(z, X, Y) => "
addClause "![X, Y, Z] : (p(X,Y,Z) => p(s(X),Y,s(Z)))"

val goal = mkGoal "p(z, z, z)"
I.simpleProve ($goal)

val goal = mkGoal `"p(X, z, X) => p(s(X), z, s(X))"
I.simpleProve ($goal)

addClause "![X] : p(X, z, X)"

val goal = mkGoal "![Y] : ?[Z] : p(z, Y, Z)"
I.simpleProve ($goal)

val goal = mkGoal "![Y] : ?[Z] : p(X, Y, Z) => ![Y] : ?[Z] : p(s(X), Y, Z)"
I.simpleProve ($goal)

addClause "![X, Y] : ?[Z] : p(X, Y, Z)"

val goal = mkGoal "![Y] : (p(z, Y, Y) => p(z, s(Y), s(Y)))"
I.simpleProve ($goal)

val goal = mkGoal "p(s(X), Y, s(Z)) => p(X, s(Y), s(Z)) => p(s(X), s(Y), s(s(Z)))"
I.simpleProve ($goal)

addClause "![X, Y, Z] : (p(X, Y, Z) => p(X, s(Y), s(Z)))"

val goal = mkGoal "p(Y, z, Y)"
I.simpleProve ($goal)

val goal = mkGoal "p(Y, X, Z) => p(Y, s(X), s(Z))"
I.simpleProve ($goal)

val goal = mkGoal "p(s(z), M, s(M))"
I.simpleProve ($goal)

val goal = mkGoal "p(s(N), s(M), s(K)) => p(s(N), M, K) => p(s(s(N)), s(M), s(s(K)))"
I.simpleProve ($goal)

addClause "![X, Y, Z] : (p(X, s(Y), Z) => p(s(X), Y, Z))"


PP.pp(F.pp goal)

