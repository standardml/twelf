structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
     let
	(* open MLton *)
	val _ =
	   MLton.Cont.callcc
	   (fn k =>
	    MLton.Signal.setHandler
	    (Posix.Signal.int,
	     MLton.Signal.Handler.handler
		 (fn _ =>
		     MLton.Thread.prepare
		     (MLton.Thread.new (fn () => MLton.Cont.throw (k, ())),
		      ()))))
     in
	loop ()
     end

end;
