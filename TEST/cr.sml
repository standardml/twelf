fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

Twelf.unsafe := true;
test "examples/church-rosser/test-unsafe.cfg";
Twelf.unsafe := false;