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
   structure TpRecon : TP_RECON
     sharing TpRecon.IntSyn = IntSyn'
     sharing type TpRecon.term = Parser.ExtSyn.term
     sharing type TpRecon.query = Parser.ExtSyn.query
     (* sharing type TpRecon.Paths.occConDec = Origins.Paths.occConDec *)
   structure Timers : TIMERS
   structure CompSyn : COMPSYN
     sharing CompSyn.IntSyn = IntSyn'
   structure Compile : COMPILE
     sharing Compile.IntSyn = IntSyn'
     sharing Compile.CompSyn = CompSyn
   structure CPrint : CPRINT
     sharing CPrint.IntSyn = IntSyn'
     sharing CPrint.CompSyn = CompSyn
   structure CSManager : CS_MANAGER
     sharing CSManager.IntSyn = IntSyn'
   structure AbsMachine : ABSMACHINE
     sharing AbsMachine.IntSyn = IntSyn'
     sharing AbsMachine.CompSyn = CompSyn
   structure Tabled : TABLED
     sharing Tabled.IntSyn = IntSyn'
     sharing Tabled.CompSyn = CompSyn
   structure TableIndex : TABLEINDEX
     sharing TableIndex.IntSyn = IntSyn'
   structure Strict : STRICT
     sharing Strict.IntSyn = IntSyn'
     sharing Strict.Paths = TpRecon.Paths
   structure Print : PRINT
     sharing Print.IntSyn = IntSyn')
 : SOLVE =
struct

  structure IntSyn = IntSyn'
  structure ExtSyn = TpRecon
  structure Paths = TpRecon.Paths
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

  (* checkStages : bound * int -> unit *)
  (* raises AbortQuery(msg) if the actual #stages do not match *)
  (* the expected number, given the bound on the number of tries *)
  (* dummy currently -bp *)
  fun checkStages (try, stages) = 
     if boundEq (try, SOME(stages))
	then ()
      else raise AbortQuery ("Query error -- wrong number of stages: "
			     ^ boundToString try ^ " tries, but terminated after  "
			     ^ Int.toString stages)

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
	(* use region information! *)
	val (A, NONE, Xs) =
	      TpRecon.queryToQuery (TpRecon.query(NONE, solve),
                                    Paths.Loc (fileName, r))
					(* times itself *)
	(* echo declaration, according to chatter level *)
	val _ = if !Global.chatter >= 2
		  then print ("%solve ")
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
	CSManager.reset ();
	((* Call to solve raises Solution _ if there is a solution,
	  returns () if there is none.  It could also not terminate
	  *)
	 (Timers.time Timers.solving AbsMachine.solve)
	 ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
	  scInit);		
	 raise AbortQuery ("No solution to %solve found"))
	handle Solution (i,(U,V)) =>
	  let
	    val conDec = ((Strict.check ((U, V), NONE); 
	                   IntSyn.ConDef (name, NONE, i, U, V, IntSyn.Type)) 
			  handle Strict.Error _ => 
			    IntSyn.AbbrevDef (name, NONE, i, U, V, IntSyn.Type))
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
	    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
	    val (A, optName, Xs) = TpRecon.queryToQuery(quy, Paths.Loc (fileName, r))
					(* times itself *)
	    val _ = if !Global.chatter >= 2
		      then print ("%query " ^ boundToString expected
					 ^ " " ^ boundToString try ^ "\n")
		    else ()
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
		     then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
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
		  then (CSManager.reset ();
			(* solve query if bound > 0 *)
			((Timers.time Timers.solving AbsMachine.solve)
			 ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
			  scInit)) handle Done => (); (* printing is timed into solving! *)
			CSManager.reset ();	(* in case Done was raised *)
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


  (* bp *)
      fun querytabled ((try, quy), Paths.Loc (fileName, r)) =
	  let
	    val _ = if !Global.chatter >= 2
		      then print ("%querytabled " ^ boundToString try)
		    else ()
	    (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
	    val (A, optName, Xs) = TpRecon.queryToQuery(quy, Paths.Loc (fileName, r))
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

	     (* is g always atomic ? - NO! too restrictive, might want to solve
                universally quantified statements - bp *)
(*
	     val CompSyn.Atom(p') = g
	     val (p,s) = Abstract.abstractEVarEClo (p',IntSyn.id)
*)
			
	     (* solutions = ref <n> counts the number of solutions found *)
	     (* -bp redundant ? *)
	     val solutions = ref 0
	     val status = ref false
	     val uniquesol = ref 0

	     (* stage = ref <n> counts the number of stages found *)
	     val stages = ref 1

	     (* Initial success continuation prints substitution (according to chatter level)
		and raises exception Done if bound has been reached, otherwise it returns
                to search for further solutions
              *)
	      fun scInit M =
		  (solutions := !solutions+1;	 
		   
		   if !Global.chatter >= 3
		     then (print ("\n---------- Solutions " ^ Int.toString (!solutions) ^ 
				  " ----------\n");
			   print ((Timers.time Timers.printing evarInstToString) Xs ^ " \n"))
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
		     then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
		            of NONE => ()
			     | SOME(str) =>
			       print ("Remaining constraints:\n"
				      ^ str ^ "\n")
		   else ())
              (* loops -- scinit will raise exception Done *)
	      fun loop () =  (if exceeds (SOME(!stages-1),try)
				then (print ("\n ================= " ^
					     " Number of tries exceeds stages " ^ 
					     " ======================= \n");  
				      status := false;
				      raise Done)
			      else ();								
				print ("\n ====================== Stage " ^ 
				       Int.toString(!stages) ^ " finished =================== \n");
			      if Tabled.nextStage () then 
				(stages := (!stages) + 1;
				 loop ())
			      else 
				(* table did not change, 
				 * i.e. all solutions have been found 
				 * we check for *all* solutions
				 *)
				status := true;
				raise Done) 
	      val _ = Tabled.reset ()
              in
		if not (boundEq (try, SOME(0)))
		  then (CSManager.reset ();
			(* solve query if bound > 0 *)
			(Timers.time Timers.solving Tabled.solve)  
			((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), 
			  scInit) handle Done => (); (* printing is timed into solving! *) 

			CSManager.reset (); 	(* in case Done was raised *)
			(* next stage until table doesn't change *)
			loop();
		        checkStages (try, !stages)  
			)
		    handle Done => ()
		else if !Global.chatter >= 3
		       then print ("Skipping query (bound = 0)\n")
		     else if !Global.chatter >= 2
			    then print ("skipping")
			  else ();
		if !Global.chatter >= 3
		  then 
		    (TableIndex.printTable();
		     print "\n____________________________________________\n\n";
		     print ("number of stages: tried "    ^ boundToString try ^ " \n" ^ 
			    "terminated after " ^ Int.toString (!stages) ^ " stages \n \n");
		     (if (!status) then 
			print "Tabled evaluation COMPLETE \n \n"
		      else 
			print "Tabled evaluation NOT COMPLETE \n \n");
		     print "\n____________________________________________\n\n";
		     print "\n Table Indexing parameters: \n";
		     (case (!TableIndex.strategy) of
			    TableIndex.Variant =>  print "\n       Table Strategy := Variant \n"
			 |  TableIndex.Subsumption => print "\n       Table Strategy := Subsumption \n");
		     (case (!TableIndex.termDepth) of
			    NONE => print ("\n       Term Depth Abstraction := NONE \n")
			  | SOME(d) => print ("\n       Term Depth Abstraction := " ^
					       Int.toString(d) ^ "\n"));
		     (if (!TableIndex.strengthen) then 
			print "\n       Strengthening := true \n"
		      else 
			print "\n       Strengthening := false \n");

		     print "\n____________________________________________\n\n")
		else if !Global.chatter >= 2
		       then print (" OK\n")
		     else ()
              end



  (* Interactive Query Top Level *)

  fun qLoop () = qLoops (CSManager.reset ();
                         Parser.parseTerminalQ ("?- ", "   ")) (* primary, secondary prompt *)
  and qLoops (s) = qLoops' ((Timers.time Timers.parsing S.expose) s)
  and qLoops' (S.Empty) = true		(* normal exit *)
    | qLoops' (S.Cons (query, s')) =
      let
	val (A, optName, Xs) = TpRecon.queryToQuery(query, Paths.Loc ("stdIn", Paths.Reg (0,0)))
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
	       then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
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
