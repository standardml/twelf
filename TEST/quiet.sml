(* Quiet regression test *)
(* Does not call "use", exits when it is done: suitable for mlton or sml/nj *)
(* Author: Robert J. Simmons *)

local
  val _ = Twelf.chatter := 0
  val _ = Twelf.doubleCheck := true
  val errors = ref 0
  fun reportError(file) = 
	(errors := !errors + 1;
	 print ("Regression test failed on "^file^"\n"))
in

val test = fn (file) =>
    let
       val stat = Twelf.make file 
		      handle _ => Twelf.ABORT
    in 
      case stat
        of Twelf.OK => Twelf.OK
         | Twelf.ABORT => (reportError (file); Twelf.ABORT)
    end;

fun testUnsafe (file) = 
    let
       val _ = Twelf.unsafe := true
       val stat = Twelf.make file 
		      handle e => Twelf.ABORT
       val _ = Twelf.unsafe := false
    in 
       case stat 
         of Twelf.OK => Twelf.OK
          | Twelf.ABORT => (reportError (file); Twelf.ABORT)
    end;

val conclude : unit -> unit = fn () =>
   case (!errors) of 
         0 => (print ("Test complete with no errors\n"); 
	       OS.Process.exit OS.Process.success)
       | 1 => (print ("Test complete with 1 error\n");
	       OS.Process.exit OS.Process.failure)
       | n => (print ("Test complete with "^(Int.toString n)^" errors\n");
	       OS.Process.exit OS.Process.failure);

end; (* local... *)
