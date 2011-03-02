(* Quiet regression test *)
(* Does not call "use", exits when it is done: suitable for mlton or sml/nj *)
(* Author: Robert J. Simmons *)

structure RegressionTest = struct

 local
   val _ = Twelf.chatter := 0
   val errors = ref 0
   fun reportError(file) = 
	 (errors := !errors + 1;
	  print ("Regression test failed on "^file^"\n"))
 in
 
 fun test (file) =
     let
	 val _ = print ("Test:        "^file) 
	 val stat = Twelf.make file 
	     handle _ => Twelf.ABORT
     in 
	 case stat
	  of Twelf.OK => Twelf.OK
	   | Twelf.ABORT => (reportError (file); Twelf.ABORT)
     end;
     
 fun testUnsafe (file) = 
     let
	 val _ = print ("Test Unsafe: "^file) 
	 val _ = Twelf.unsafe := true 
	 val stat = Twelf.make file 
	     handle e => Twelf.ABORT
	 val _ = Twelf.unsafe := false
     in 
	 case stat 
          of Twelf.OK => Twelf.OK
           | Twelf.ABORT => (reportError (file); Twelf.ABORT)
     end;
    
 val conclude : unit -> OS.Process.status = 
  fn () =>
     let val err = !errors 
     in
       errors := 0;
       case (err) of 
	 0 => (print ("Test complete with no errors\n"); OS.Process.success)
       | 1 => (print ("Test complete with 1 error\n"); OS.Process.failure)
       | n => (print ("Test complete with "^(Int.toString n)^" errors\n");
	       OS.Process.failure)
     end

 fun process (filename) = 
     let 
	 val file = TextIO.openIn filename
	 fun runline (str : string) =
	     if String.isPrefix "#" str 
	     then NONE
	     else if String.isPrefix "testUnsafe" str 
	     then SOME(testUnsafe 
			   (String.extract(str,11,SOME(String.size str - 12))))
	     else if String.isPrefix "test" str
	     then SOME(test(String.extract(str,5,SOME(String.size str - 6))))
	     else NONE (* Ignore any non-standard line *)

         exception Aborted

	 fun getstatus (status,msg) = 
	     case status of 
		 NONE => ()
	       | SOME(Twelf.OK) => print ("..."^msg)
	       | SOME(Twelf.ABORT) => print ("...ABORT!\n"; raise Aborted)

	 fun readfile() = 
	     case TextIO.inputLine file of
		 NONE => (TextIO.closeIn file; conclude())
	       | (SOME s) => 
                 let in
                   Twelf.doubleCheck := false;
                   getstatus(runline s, "OK.\n"); 
                   Twelf.doubleCheck := true;
                   getstatus(runline s, "Double checked.\n");
                   readfile()
                 end handle Aborted => readfile()
     in
	 readfile()
     end		     
          
 end (* local... *)

end (* structure RegressionTest *)

