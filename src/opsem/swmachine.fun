functor SwMachine (structure Trace : TRACE
                   structure AbsMachine : ABSMACHINE
                   structure TMachine : ABSMACHINE
                   (*! sharing TMachine.IntSyn = AbsMachine.IntSyn !*)
                   (*! sharing TMachine.CompSyn = AbsMachine.CompSyn !*)
                     ) : ABSMACHINE =
struct

  (*! structure IntSyn = AbsMachine.IntSyn !*)
  (*! structure CompSyn = AbsMachine.CompSyn !*)

  fun solve args =
    if Trace.tracing ()
      then TMachine.solve args
    else  AbsMachine.solve args

end;  (* functor SwMachine *)

