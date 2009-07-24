
structure Timers : TIMERS =
struct

  val centers : Timing.center list ref = ref []

  fun add_timer name =
      let
        val center = Timing.newCenter name
      in
        centers := !centers @ [center];
        center
      end

  val checking    = add_timer ("Checking      ")
  val eta_normal  = add_timer ("Eta Normal    ")
  val printing    = add_timer ("Printing      ")
  val translation = add_timer ("Translation   ")

  val total    = Timing.sumCenter ("Total         ", !centers)

  val time = Timing.time

  fun reset () = List.app Timing.reset (!centers)

  fun check () =
      (List.app (print o Timing.toString) (!centers);
       print (Timing.sumToString total))

  fun show () = (check (); reset ()) 

end
