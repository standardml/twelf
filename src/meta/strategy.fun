(* MTP Strategy: Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTPStrategy (structure MTPGlobal : MTPGLOBAL
		     structure StateSyn' : STATESYN
		     structure MTPFilling : MTPFILLING
		       sharing MTPFilling.StateSyn = StateSyn'
		     structure MTPSplitting : MTPSPLITTING
	  	       sharing MTPSplitting.StateSyn = StateSyn'
		     structure MTPRecursion : MTPRECURSION
		       sharing MTPRecursion.StateSyn = StateSyn'
		     structure MTPrint : MTPRINT
		       sharing MTPrint.StateSyn = StateSyn'
		     structure Timers : TIMERS) 
  : MTPSTRATEGY =
struct

  structure StateSyn = StateSyn'

  local

    structure S = StateSyn

    fun printInit () = 
        if !Global.chatter > 3 then print "Strategy\n"
	else ()

    fun printFilling () = 
        if !Global.chatter > 5 then print ("[Filling ... ")
	else if !Global.chatter> 4 then print ("F")
	     else  ()

    fun printRecursion () = 
        if !Global.chatter > 5 then print ("[Recursion ...")
	else if !Global.chatter> 4 then print ("R")
	     else ()

    fun printSplitting splitOp = 
        if !Global.chatter > 5 then print ("[" ^ MTPSplitting.menu splitOp)
	else if !Global.chatter> 4 then print ("S")
	     else ()

    fun printCloseBracket () = 
        if !Global.chatter > 5 then print ("]\n")
	else ()

    fun printQed () = 
        if !Global.chatter > 3 then print ("[QED]\n")
	else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun findMin nil = NONE
      | findMin L =
	  let 
	    fun findMin' (nil, result) = result
	      | findMin' (O' :: L', NONE) =
	        if MTPSplitting.applicable O' then 
		   findMin' (L', SOME O')
		else findMin' (L', NONE)
	      | findMin' (O' :: L', SOME O) =
	        if MTPSplitting.applicable O' then
		  case MTPSplitting.compare (O', O)
		    of LESS =>  findMin' (L', SOME O')
		     | _ => findMin' (L', SOME O)
		else findMin' (L', SOME O)

	  in
	    findMin' (L, NONE)
	  end

    (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
	 contains the states resulting from givenStates which cannot be 
	 solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and 
	 contains the states resulting from givenStates which can be 
	 solved using Filling, Recursion, and Splitting
    *)
    fun split (S :: givenStates, os as (openStates, solvedStates)) =
	case findMin ((Timers.time Timers.splitting MTPSplitting.expand) S) of 
	  NONE => fill (givenStates, (S :: openStates, solvedStates))
	| SOME splitOp =>
	    let 
	      val _ = printSplitting splitOp
	      val SL = (Timers.time Timers.splitting MTPSplitting.apply) splitOp
	      val _ = printCloseBracket ()
	      val SL' = map (fn S => (Timers.time Timers.recursion MTPRecursion.apply) (MTPRecursion.expand S)) SL
	    in
	      fill (SL' @ givenStates, os)
	    end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion MTPFilling.expand) S
	  of fillingOp =>
	     (let
	       val _ = printFilling ()
	       val P = (Timers.time Timers.filling MTPFilling.apply) fillingOp
	       val _ = printCloseBracket ()
	      in
		fill (givenStates, os)
	      end) handle MTPFilling.Error _ => split (S :: givenStates, os)

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be 
	 solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be 
	 solved using Filling, Recursion, and Splitting
     *)       
    fun run givenStates = 
        let
	  val _ = printInit ()
	  val os = fill (givenStates, (nil, nil))
	  val _ = case os
	            of (nil, _) => printQed ()
		     | _ => ()
	in
	  os
	end

  in
    val run = run
  end (* local *)
end;  (* functor StrategyFRS *)


