(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)

Twelf.chatter := 3; 

Twelf.doubleCheck := true;

fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

test "examples/tabled/tests/tab.cfg";
test "examples/tabled/church-rosser/tab.cfg";
test "examples/tabled/subtype1/tab.cfg";
test "examples/tabled/subtype/tab.cfg";


