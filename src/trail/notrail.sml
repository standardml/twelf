(* Not Trailing Abstract Operations *)
(* Author: Roberto Virga *)

structure NoTrail : TRAIL =
struct

  type 'a trail = unit

  fun trail () = ()
  
  fun reset () = ()

  fun mark () = ()

  fun unwind ((), undo) = ()

  fun log ((), action) = ()
end; (* structure NoTrail *)
