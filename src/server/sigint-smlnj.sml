structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
      (SMLofNJ.Cont.callcc
       (fn k => (Signals.setHandler (Signals.sigINT,
				     Signals.HANDLER (fn _ => (print "\ninterrupt\n"; k)));
		 ()));
       loop ())

end;  (* structure SigINT *)
