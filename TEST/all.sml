(* (Outdated) Regression test - *)
(* Author: Frank Pfenning *)

(* Twelf.chatter := 0; *)
(* Twelf.chatter := 1; *)
(* Twelf.chatter := 2; *)
(* Twelf.chatter := 5; *)
Twelf.doubleCheck := true;

fun test (file) =
    case Twelf.make file
      of Twelf.OK => Twelf.OK
       | Twelf.ABORT => raise Domain;

fun testUnsafe (file) = 
    let
       val _ = Twelf.unsafe := true
       val stat = Twelf.make file 
		      handle e => (Twelf.unsafe := false; raise e)
       val _ = Twelf.unsafe := false
    in 
       case stat 
         of Twelf.OK => Twelf.OK
          | Twelf.ABORT => raise Domain
    end;

fun conclude () = ();

use "TEST/regression.sml";
