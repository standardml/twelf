Twelf.make "examples-hlf/hsubst/hsubst.cfg";
fun check file = (case Twelf.make file 
                   of Twelf.OK => ()
		    | Twelf.ABORT => raise Domain);

Twelf.chatter := 1;
check "examples-hlf/lincut/lincut.cfg";
check "examples-hlf/miniml/sources.cfg";
check "examples-hlf/miniml-ext/sources.cfg";
check "examples-hlf/negfocus/sources.cfg";
check "examples-hlf/petri/sources.cfg";
check "examples-hlf/sill/sill.cfg"; 
check "examples-hlf/weakfocus/pers.cfg";
