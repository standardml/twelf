structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
     let
	(* open MLton *)
	val _ =
	   MLton.Cont.callcc
	   (fn k =>
	    MLton.Signal.handleWith'
	    (MLton.Signal.int, fn _ =>
	     MLton.Thread.new (fn () => MLton.Cont.throw (k, ()))))
     in
	loop ()
     end

end;
