(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow *)

functor Solve
  (structure Global : GLOBAL
   structure IntSyn' : INTSYN
   structure Names : NAMES
     sharing Names.IntSyn = IntSyn'
   structure Parser : PARSER
     sharing Parser.Names = Names
   structure Constraints : CONSTRAINTS		
     sharing Constraints.IntSyn = IntSyn'
   structure Abstract : ABSTRACT
     sharing Abstract.IntSyn = IntSyn'
   structure TpReconQ : TP_RECON
     sharing TpReconQ.IntSyn = IntSyn'
     sharing type TpReconQ.term = Parser.ExtSynQ.term
     sharing type TpReconQ.query = Parser.ExtSynQ.query
     (* sharing type TpReconQ.Paths.occConDec = Origins.Paths.occConDec *)
   structure Timers : TIMERS
   structure CompSyn : COMPSYN
     sharing CompSyn.IntSyn = IntSyn'
   structure Compile : COMPILE
     sharing Compile.IntSyn = IntSyn'
     sharing Compile.CompSyn = CompSyn
   structure Trail : TRAIL
     sharing Trail.IntSyn = IntSyn'
   structure AbsMachine : ABSMACHINE
     sharing AbsMachine.IntSyn = IntSyn'
     sharing AbsMachine.CompSyn = CompSyn
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn')
 : SOLVE =
struct

  structure IntSyn = IntSyn'
  structure ExtSynQ = TpReconQ
  structure Paths = TpReconQ.Paths
  structure S = Parser.Stream

  (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun evarInstToString (Xs) =
      if !Global.chatter >= 3
	then Print.evarInstToString (Xs)
      else ""

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun expToString GU =
      if !Global.chatter >= 3
	then Print.expToString GU
      else ""

  (* exception AbortQuery
     is raised when a %query declaration has an unexpected number of solutions
     or of %solve has no solution.
  *)
  exception AbortQuery of string

  (* Bounds SOME(n) for n >= 0, NONE represents positive infinity *)
  (* Concrete syntax: 0, 1, 2, ..., * *)
  type bound = int option

  (* exceeds : bound * bound -> bool *)
  fun exceeds (SOME(n), SOME(m)) = (n >= m)
    | exceeds (SOME(n), NONE) = false
    | exceeds (NONE, _) = true

  (* boundEq : bound * bound -> bool *)
  fun boundEq (SOME(n), SOME(m)) = (n = m)
    | boundEq (NONE, NONE) = true
    | boundEq _ = false

  (* boundToString : bound -> string *)
  fun boundToString (SOME(n)) = Int.toString (n)
    | boundToString (NONE) = "*"

  (* boundMin : bound * bound -> bound *)
  fun boundMin (SOME(n), SOME(m)) = SOME(Int.min (n,m))
    | boundMin (b, NONE) = b
    | boundMin (NONE, b) = b

  (* checkSolutions : bound * bound * int -> unit *)
  (* raises AbortQuery(msg) if the actual solutions do not match *)
  (* the expected number, given the bound on the number of tries *)
  fun checkSolutions (expected, try, solutions) =
      if boundEq (boundMin (expected, try), SOME(solutions))
	then ()
      else raise AbortQuery ("Query error -- wrong number of solutions: expected "
			     ^ boundToString expected ^ " in "
			     ^ boundToString try ^ " tries, but found "
			     ^ Int.toString solutions)

  (* moreSolutions () = b  iff  the user requests more solutions
     Effects: inputs one line from standard input,
              raises exception AbortQuery(msg) is first character is "q" or "Q"
  *)
  fun moreSolutions () =
      (print ("More? ");
       case String.sub (TextIO.inputLine (TextIO.stdIn), 0)
	 of #"y" => true
          | #"Y" => true
	  | #";" => true
	  | #"q" => raise AbortQuery("Query error -- explicit quit")
	  | #"Q" => raise AbortQuery("Query error -- explicit quit")
	  | _ => false)

  (* exception Done is raised by the initial success continuation
     when no further solutions are requested.
  *)
  exception Done

  (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)
  exception Solution of int * (IntSyn.Exp * IntSyn.Exp)

  (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)
  fun solve ((name, solve), Paths.Loc (fileName, r)) =
      let
	val _ = if !Global.chatter >= 2
		  then print ("%solve")
		else ()
	(* use region information! *)
	val (A, NONE, Xs) =
	       TpReconQ.queryToQuery(TpReconQ.query(NONE,solve), Paths.Loc (fileName, r))
					(* times itself *)

	(* echo declaration, according to chatter level *)
	val _ = if !Global.chatter >= 2
		  then print (" ")
		else ()
	val _ = if !Global.chatter >= 3
		  then print ("\n"
				     ^ (Timers.time Timers.printing expToString)
				     (IntSyn.Null, A)
				     ^ ".\n")
		else ()

	val g = (Timers.time Timers.compiling Compile.compileGoal) 
	            (IntSyn.Null, A)

	(* 
	   the initial success continuation builds the abstractions to we can
	   define c = M' : A', where A' is a solution for A and M' the proof term.
	*)
	fun scInit M =
	    raise Solution (((Timers.time Timers.abstract Abstract.abstractDef) (M, A))
			    handle Abstract.Error (msg)
			    => raise Abstract.Error (Paths.wrap (r, msg)))
      in
	Trail.reset ();
	((* Call to solve raises Solution _ if there is a solution,
	  returns () if there is none.  It could also not terminate
	  *)
	 (Timers.time Timers.solving AbsMachine.solve)
	 ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
	  scInit);		
	 raise AbortQuery ("No solution to %solve found"))
	handle Solution (i,(U,V)) =>
	  let
	    val conDec = IntSyn.ConDef (name, i, U, V, IntSyn.Type)
	  in
	    conDec
	  end  (* solve _ handle Solution => _ *)
	  (* for frontend.fun:
	    val _ = Strict.check (conDec, NONE)
	    (* allocate cid after strictness has been checked! *)
	    val cid = installConDec (conDec, NONE)
	    val _ = if !Global.chatter >= 3
		      then print ((Timers.time Timers.printing Print.conDecToString)
					 conDec ^ "\n")
		    else if !Global.chatter >= 2
			   then print (" OK\n")
			 else ();
	  *)
      end

	    (* %query <expected> <try> A or %query <expected> <try> X : A *)
      fun query ((expected, try, quy), Paths.Loc (fileName, r)) =
	  let
	    val _ = if !Global.chatter >= 2
		      then print ("%query " ^ boundToString expected
					 ^ " " ^ boundToString try)
		    else ()
	    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
	    val (A, optName, Xs) = TpReconQ.queryToQuery(quy, Paths.Loc (fileName, r))
					(* times itself *)
	    val _ = if !Global.chatter >= 2
		      then print (" ")
		    else ()
	    val _ = if !Global.chatter >= 3
		      then print ("\n" ^ (Timers.time Timers.printing expToString)
				  (IntSyn.Null, A) ^ ".\n")
		    else ()
	    (* Problem: we cannot give an answer substitution for the variables
	       in the printed query, since the new variables in this query
               may not necessarily have global scope.

               For the moment, we print only the answer substitution for the
               original variables encountered during parsing.
	     *)
	     (*
		val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
	     *)
	     val g = (Timers.time Timers.compiling Compile.compileGoal) 
	                (IntSyn.Null, A)

	     (* solutions = ref <n> counts the number of solutions found *)
	     val solutions = ref 0

	     (* Initial success continuation prints substitution (according to chatter level)
		and raises exception Done if bound has been reached, otherwise it returns
                to search for further solutions
              *)
	      fun scInit M =
		  (solutions := !solutions+1;
		   if !Global.chatter >= 3
		     then (print ("---------- Solution " ^ Int.toString (!solutions) ^ " ----------\n");
			   print ((Timers.time Timers.printing evarInstToString) Xs ^ "\n"))
		   else if !Global.chatter >= 2
			  then print "."
			else ();
		   case optName
		     of NONE => ()
		      | SOME(name) =>
		        if !Global.chatter >= 3
			  then print ((Timers.time Timers.printing evarInstToString)
					     [(M, name)] ^ "\n")
			else ();
		   if !Global.chatter >= 3
		     (* Question: should we collect constraints in M? *)
		     then case (Timers.time Timers.printing Print.evarConstrToStringOpt) Xs
		            of NONE => ()
			     | SOME(str) =>
			       print ("Remaining constraints:\n"
				      ^ str ^ "\n")
		   else ();
		   if exceeds (SOME(!solutions),try)
		     then raise Done
		   else ())
              in
		if not (boundEq (try, SOME(0)))
		  then (Trail.reset ();
			(* solve query if bound > 0 *)
			((Timers.time Timers.solving AbsMachine.solve)
			 ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
			  scInit)) handle Done => (); (* printing is timed into solving! *)
			Trail.reset ();	(* in case Done was raised *)
			(* check if number of solutions is correct *)
		        checkSolutions (expected, try, !solutions))
		else if !Global.chatter >= 3
		       then print ("Skipping query (bound = 0)\n")
		     else if !Global.chatter >= 2
			    then print ("skipping")
			  else ();
		if !Global.chatter >= 3
		  then print "____________________________________________\n\n"
		else if !Global.chatter >= 2
		       then print (" OK\n")
		     else ()
              end

  (* Interactive Query Top Level *)

  fun qLoop () = qLoops (Parser.parseTerminalQ ("?- ", "   ")) (* primary, secondary prompt *)
  and qLoops (s) = qLoops' ((Timers.time Timers.parsing S.expose) s)
  and qLoops' (S.Empty) = true		(* normal exit *)
    | qLoops' (S.Cons (query, s')) =
      let
	val (A, optName, Xs) = TpReconQ.queryToQuery(query, Paths.Loc ("stdIn", Paths.Reg (0,0)))
					(* times itself *)
	val g = (Timers.time Timers.compiling Compile.compileGoal) 
	            (IntSyn.Null, A)
	fun scInit M =
	    (print ((Timers.time Timers.printing evarInstToString) Xs ^ "\n");
	     case optName
	       of NONE => ()
		| SOME(name) =>
		  if !Global.chatter >= 3
		    then print ((Timers.time Timers.printing evarInstToString)
				       [(M, name)] ^ "\n")
		  else ();
	     if !Global.chatter >= 3
	       (* Question: should we collect constraints from M? *)
	       then case (Timers.time Timers.printing Print.evarConstrToStringOpt) Xs
		      of NONE => ()
		       | SOME(str) =>
			 print ("Remaining constraints:\n"
				^ str ^ "\n")
	     else ();
	     if moreSolutions () then () else raise Done)
	val _ = if !Global.chatter >= 3
		  then print "Solving...\n"
		else ()
      in
	((Timers.time Timers.solving AbsMachine.solve)
	 ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit); (* scInit is timed into solving! *)
	 print "No more solutions\n")
	handle Done => ();
	(* Ignore s': parse one query at a time *)
	qLoop ()
      end

end; (* functor Solve *)
