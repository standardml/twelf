(* Meta Theorem Prover Version 1.3 *)
(* Author: Carsten Schuermann *)

functor MTProver (structure FunSyn' : FUNSYN
		  structure StateSyn' : STATESYN
		    sharing StateSyn'.FunSyn = FunSyn'
		  structure MTPInit : MTPINIT
		    sharing MTPInit.FunSyn = FunSyn'
		    sharing MTPInit.StateSyn = StateSyn'
		  structure MTPFilling : MTPFILLING
		    sharing MTPFilling.StateSyn = StateSyn'
		  structure MTPSplitting : MTPSPLITTING
		    sharing MTPSplitting.StateSyn = StateSyn'
		  structure MTPRecursion : MTPRECURSION
		    sharing MTPRecursion.StateSyn = StateSyn'
		  structure MTPrint : MTPRINT
		    sharing MTPrint.StateSyn = StateSyn')
  : MTPROVER =
struct
  structure FunSyn = FunSyn'
  structure StateSyn = StateSyn'

  exception Error of string 

  local
    structure F = FunSyn
    structure S = StateSyn 


    fun recursion S = 
      let 
	val operator = MTPRecursion.expand S
      in
	(TextIO.print ("\n++++++\n" ^ MTPrint.stateToString (MTPRecursion.apply operator) ^ "\n++++++\n\n" ))
      end


    fun app operator =
      let 
	val Ss = MTPSplitting.apply operator
	val _ = map (fn S => (TextIO.print (MTPrint.stateToString S ^ "\n\n\n"); recursion S)) Ss
      in
	TextIO.print ("=================\n")
      end

    fun split S =
      let 
	val operators = MTPSplitting.expand S
      in
	map (fn operator => (TextIO.print (MTPSplitting.menu operator ^ "\n"); app operator)) operators
      end
      
    fun fill S =
      let
	val operator = MTPFilling.expand S
      in 
	if MTPFilling.apply operator then TextIO.print "[QED]\n"
	else TextIO.print "* a proof could not be found\n"
      end

    fun init (F, O) = 
      (map (fn S => (TextIO.print (MTPrint.stateToString S ^ "\n"); split (* fill *) S)) 
          (MTPInit.init (F, O)) ; TextIO.print "\n")


  in
    val init = init
  end (* local *)
end (* functor MTProver *)