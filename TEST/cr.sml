fun test (file) =
    case Twelf.Config.load (Twelf.Config.read file)
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

Global.safe := false;
test "examples/church-rosser/test-cr.cfg";
