structure SigINT :> SIGINT =
struct

  fun interruptLoop (loop:unit -> unit) =
     let
     in
	loop ()
     end

end;
