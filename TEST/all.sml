(* Global.chatter := 0; *)
(* Global.chatter := 1; *)
(* Global.chatter := 2; *)
(* Global.chatter := 3; *)

fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

test "examples/arith/test.cfg";
test "examples/ccc/test.cfg";
test "examples/church-rosser/test.cfg";
test "examples/compile/cls/test.cfg";
test "examples/compile/cpm/test.cfg";
test "examples/compile/cps/test.cfg";
test "examples/compile/cxm/test.cfg";
test "examples/compile/debruijn/test.cfg";
test "examples/compile/debruijn1/test.cfg";
(* cut-elim not in original test suite, ~1 secs more *)
test "examples/cut-elim/test.cfg";
(* fol not in original test suite, ~14 secs more *)
test "examples/fol/test.cfg";
(* guide not in test suite, ~.05 secs more *)
test "examples/guide/test.cfg";
test "examples/lp/test.cfg";
test "examples/lp-horn/test.cfg";
test "examples/mini-ml/test.cfg";
test "examples/polylam/test.cfg";
test "examples/prop-calc/test.cfg";
test "examples/units/test.cfg";
