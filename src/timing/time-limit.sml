(* time-limit.sml
 *
 * COPYRIGHT (c) 1993 by AT&T Bell Laboratories.  See COPYRIGHT file for details.
 * Modified: Brigitte Pientka
 *)

structure TimeLimit : sig
    exception TimeOut
    val timeLimit : Time.time option -> ('a -> 'b) -> 'a -> 'b
  end = struct

    exception TimeOut

    fun timeLimit NONE f x = f x
      | timeLimit (SOME t) f x = 
      let
	val _ = print ("TIME LIMIT : " ^ Time.toString t ^ "sec \n")
	val setitimer = SMLofNJ.IntervalTimer.setIntTimer

	fun timerOn () = ignore(setitimer (SOME t))

	fun timerOff () = ignore(setitimer NONE)

	val escapeCont = SMLofNJ.Cont.callcc (fn k => (
		SMLofNJ.Cont.callcc (fn k' => (SMLofNJ.Cont.throw k k'));
		timerOff();
		raise TimeOut))

	fun handler _ = escapeCont

      in
	Signals.setHandler (Signals.sigALRM, Signals.HANDLER handler);
	timerOn(); 
	((f x) handle ex => (timerOff(); raise ex))
	  before timerOff()
      end

  end; (* TimeLimit *)
