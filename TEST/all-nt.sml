(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)
Twelf.chatter := 5;
Twelf.doubleCheck := true;

fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

(* Examples, part of the distribution *)
(* test "examples\\arith\\test.cfg"; *)
test "examples\\ccc\\test.cfg";
test "examples\\church-rosser\\test.cfg";
test "examples\\compile\\cls\\test.cfg";
test "examples\\compile\\cpm\\test.cfg";
test "examples\\compile\\cps\\test.cfg";
test "examples\\compile\\cxm\\test.cfg";
test "examples\\compile\\debruijn\\test.cfg";
test "examples\\compile\\debruijn1\\test.cfg";
(* cpsocc not in original test suite *)
test "examples\\cpsocc\\test.cfg";
(* cut-elim not in original test suite, ~1 secs more *)
test "examples\\cut-elim\\test.cfg";
(* fol not in original test suite, ~14 secs more *)
test "examples\\fol\\test.cfg";
(* guide not in test suite, ~.05 secs more *)
test "examples\\guide\\test.cfg";
(* incll not in original test suite, ~55secs more *)
(*test "examples\\incll\\test.cfg"; *)
(* kolm not in original test suite *)
test "examples\\kolm\\test.cfg";
test "examples\\lp\\test.cfg";
test "examples\\lp-horn\\test.cfg";
test "examples\\mini-ml\\test.cfg";
test "examples\\polylam\\test.cfg";
test "examples\\prop-calc\\test.cfg";

(* CLP Examples, part of the distribution *)
test "examples-clp\\arith\\test.cfg";
test "examples-clp\\base\\test.cfg";
test "examples-clp\\crypt\\test.cfg";
test "examples-clp\\integers\\test.cfg";
test "examples-clp\\laplace\\test.cfg";
test "examples-clp\\lists\\test.cfg";
test "examples-clp\\mortgage\\test.cfg";
test "examples-clp\\pelletier\\test.cfg";
test "examples-clp\\sieve\\test.cfg";

(* Exercises, not part of the distribution *)
(*test "exercises\\units\\test.cfg";
test "exercises\\opt-eval\\test.cfg";
*)
