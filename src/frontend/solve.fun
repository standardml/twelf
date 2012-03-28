(* Front End Interface *)
(* Author: Frank Pfenning *)
(* Modified: Carsten Schuermann, Jeff Polakow, Roberto Virga *)

functor Solve
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Parser : PARSER
     sharing Parser.Names = Names
   structure ReconQuery : RECON_QUERY
   (*! sharing ReconQuery.IntSyn = IntSyn' !*)
     sharing type ReconQuery.query = Parser.ExtQuery.query
     sharing type ReconQuery.solve = Parser.ExtQuery.solve
     sharing type ReconQuery.define = Parser.ExtQuery.define
   (* sharing type ReconQuery.Paths.occConDec = Origins.Paths.occConDec *)
   structure Timers : TIMERS
   (*! structure CompSyn : COMPSYN !*)
   (*! sharing CompSyn.IntSyn = IntSyn' !*)
   structure Compile : COMPILE
   (*! sharing Compile.IntSyn = IntSyn' !*)
   (*! sharing Compile.CompSyn = CompSyn !*)
   structure CPrint : CPRINT
   (*! sharing CPrint.IntSyn = IntSyn' !*)
   (*! sharing CPrint.CompSyn = CompSyn !*)
   (*! structure CSManager : CS_MANAGER !*)
   (*! sharing CSManager.IntSyn = IntSyn' !*)
   structure AbsMachine : ABSMACHINE
   (*! sharing AbsMachine.IntSyn = IntSyn' !*)
   (*! sharing AbsMachine.CompSyn = CompSyn !*)
   structure AbsMachineSbt : ABSMACHINESBT
    (*! sharing AbsMachineSbt.IntSyn = IntSyn' !*)
    (*! sharing AbsMachineSbt.CompSyn = CompSyn!*)
   structure PtRecon : PTRECON
   (*! sharing PtRecon.IntSyn = IntSyn' !*)
   (*! sharing PtRecon.CompSyn = CompSyn !*)
   (*! structure TableParam : TABLEPARAM !*)
   structure Tabled : TABLED
   (*! sharing Tabled.IntSyn = IntSyn' !*)
   (*! sharing Tabled.CompSyn = CompSyn !*)
   (*! structure MemoTable : MEMOTABLE !*)
    (*! sharing MemoTable.IntSyn = IntSyn' !*)
   structure Print : PRINT
   (*! sharing Print.IntSyn = IntSyn' !*)
   structure Msg : MSG)
 : SOLVE =
struct

  (*! structure IntSyn = IntSyn' !*)
  structure ExtQuery = ReconQuery
  (*! structure Paths = ReconQuery.Paths !*)
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
       case String.sub (Compat.inputLine97 (TextIO.stdIn), 0)
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

 (* exception Completed raised by tabled computation when table is saturated *)
  exception Completed

  (* exception Solution (imp, (M, A))
     is raised when M : A is the generalized form of a solution to the
     query A', where imp is the number of implicitly quantified arguments.
  *)

  exception Solution of IntSyn.Exp
  exception SolutionSkel of CompSyn.pskeleton


  (* readfile (fileName) = status
     reads and processes declarations from fileName in order, issuing
     error messages and finally returning the status (either OK or
     ABORT).
  *)
  fun solve' (defines, solve, Paths.Loc (fileName, r)) =
      let
        val (A, finish) = (* self timing *)
              ReconQuery.solveToSolve (defines, solve, Paths.Loc (fileName, r))

        (* echo declaration, according to chatter level *)
        val _ = if !Global.chatter >= 3
                  then Msg.message ("%solve ")
                else ()
        val _ = if !Global.chatter >= 3
                  then Msg.message ("\n"
                              ^ (Timers.time Timers.printing expToString)
                              (IntSyn.Null, A)
                              ^ ".\n")
                else ()
        val g = (Timers.time Timers.compiling Compile.compileGoal)
                    (IntSyn.Null, A)
        fun search () = AbsMachine.solve
                          ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                           fn M => raise Solution M)
      in
        CSManager.reset ();
        ((* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
         (TimeLimit.timeLimit (!Global.timeLimit)
         (Timers.time Timers.solving search) ());
         raise AbortQuery ("No solution to %solve found"))
        handle Solution M => (if !Global.chatter >= 3
                              then Msg.message (" OK\n")
                              else ();
                              finish M)
        handle TimeLimit.TimeOut =>
          raise AbortQuery ("\n----------- TIME OUT ---------------\n")
      end

(* Using substitution tree indexing for clauses in signature
   The logic programming interpreter then creates a proof skeleton
  and reconstructs the actual proof term which can be checked
  -- this version can be used to produce oracles, however no user
  directive is added yet.
*)
  fun solveSbt (defines, solve, Paths.Loc (fileName, r)) =
      let
        val (A, finish) = (* self timing *)
              ReconQuery.solveToSolve (defines, solve, Paths.Loc (fileName, r))

        (* echo declaration, according to chatter level *)
        val _ = if !Global.chatter >= 3
                  then Msg.message ("%solve ")
                else ()
        val _ = if !Global.chatter >= 3
                  then Msg.message ("\n" ^ (Timers.time Timers.printing expToString) (IntSyn.Null, A)
                              ^ ".\n")
                else ()

        val g = (Timers.time Timers.compiling Compile.compileGoal)
                    (IntSyn.Null, A)
      in
        CSManager.reset ();
        ((* Call to solve raises Solution _ if there is a solution,
          returns () if there is none.  It could also not terminate
          *)
         (TimeLimit.timeLimit (!Global.timeLimit))
         (Timers.time Timers.solving AbsMachineSbt.solve)
         ((g, IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
          fn Skel => raise SolutionSkel Skel);
         raise AbortQuery ("No solution to %solve found"))
        handle SolutionSkel Skel =>
          (if !Global.chatter >= 2
             then Msg.message (" OK\n")
           else ();
           ((Timers.time Timers.ptrecon PtRecon.solve)
            (Skel, (g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
             (fn (Skel, M) => raise Solution M));
               raise AbortQuery ("Proof reconstruction for %solve failed"))
             handle Solution M => finish (M))
        handle TimeLimit.TimeOut =>
          raise AbortQuery ("\n----------- TIME OUT ---------------\n" )
      end

  fun solve args =
    case (!Compile.optimize) of
      (* solves A where program clauses are indexed using substitution trees
         and reconstructs the proof term X afterwards - bp
       *)
      Compile.Indexing => solveSbt args
    | Compile.LinearHeads => solve' args
    | _ => solve' args


  (* %query <expected> <try> A or %query <expected> <try> X : A *)
  fun query' ((expected, try, quy), Paths.Loc (fileName, r)) =
    let
      (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
      val (A, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r))
      (* times itself *)
      val _ = if !Global.chatter >= 3
                then Msg.message ("%query " ^ boundToString expected
                            ^ " " ^ boundToString try ^ "\n")
              else ()
      val _ = if !Global.chatter >= 4
                then Msg.message (" ")
              else ()
      val _ = if !Global.chatter >= 3
                then Msg.message ("\n" ^ (Timers.time Timers.printing expToString)
                            (IntSyn.Null, A) ^ ".\n")
              else ()
      (* Problem: we cannot give an answer substitution for the variables
         in the printed query, since the new variables in this query
         may not necessarily have global scope.

         For the moment, we print only the answer substitution for the
         original variables encountered during parsing.
       *)
      (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs
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
           then (Msg.message ("---------- Solution " ^ Int.toString (!solutions) ^ " ----------\n");
                 Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ "\n"))
         else if !Global.chatter >= 3
                then Msg.message "."
              else ();
                case optName
                  of NONE => ()
                | SOME(name) =>
                    if !Global.chatter >= 3
                      then Msg.message ((Timers.time Timers.printing evarInstToString)
                                  [(M, name)] ^ "\n")
                        else ();
                   if !Global.chatter >= 3
                     (* Question: should we collect constraints in M? *)
                     then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                            of NONE => ()
                             | SOME(str) =>
                               Msg.message ("Remaining constraints:\n"
                                      ^ str ^ "\n")
                   else ();
                   if exceeds (SOME(!solutions),try)
                     then raise Done
                   else ())

        fun search () = AbsMachine.solve
                         ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                          scInit)
              in
                if not (boundEq (try, SOME(0)))
                  then (CSManager.reset ();
                        (* solve query if bound > 0 *)
                        ((TimeLimit.timeLimit (!Global.timeLimit)
                          (Timers.time Timers.solving search) ())
                         handle Done => () (* printing is timed into solving! *))
                        handle  TimeLimit.TimeOut =>
                          raise AbortQuery ("\n----------- TIME OUT ---------------\n" );

                        CSManager.reset ();    (* in case Done was raised *)
                        (* check if number of solutions is correct *)
                        checkSolutions (expected, try, !solutions))
                else if !Global.chatter >= 3
                       then Msg.message ("Skipping query (bound = 0)\n")
                     else if !Global.chatter >= 4
                            then Msg.message ("skipping")
                          else ();
                if !Global.chatter >= 3
                  then Msg.message "____________________________________________\n\n"
                else if !Global.chatter >= 4
                       then Msg.message (" OK\n")
                     else ()
              end

  (* %query <expected> <try> A or %query <expected> <try> X : A *)
  fun querySbt ((expected, try, quy), Paths.Loc (fileName, r)) =
    let
      (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
      val (A, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r))
      (* times itself *)
      val _ = if !Global.chatter >= 3
                then Msg.message ("%query " ^ boundToString expected
                            ^ " " ^ boundToString try ^ "\n")
              else ()
      val _ = if !Global.chatter >= 4
                then Msg.message (" ")
              else ()
      val _ = if !Global.chatter >= 3
                then Msg.message ("\n" ^ (Timers.time Timers.printing expToString)
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
           then (Msg.message ("---------- Solution " ^ Int.toString (!solutions) ^ " ----------\n");
                 Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ "\n"))
         else if !Global.chatter >= 3
                then Msg.message "."
              else ();

         case optName
           of NONE => ()
         | SOME(name) =>  (if !Global.chatter > 3
                            then
                              (Msg.message ("\n pskeleton \n");
                               Msg.message ((CompSyn.pskeletonToString M) ^ "\n"))
                          else ();

                           (Timers.time Timers.ptrecon PtRecon.solve)
                           (M, (g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                            (fn (pskel, M) => (if !Global.chatter >= 3
                                then Msg.message ((Timers.time Timers.printing evarInstToString)
                                            [(M, name)] ^ "\n")
                              else ())))) ;

             if !Global.chatter >= 3
               (* Question: should we collect constraints in M? *)
               then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                 of NONE => ()
               | SOME(str) =>
                   Msg.message ("Remaining constraints:\n"
                          ^ str ^ "\n")
             else ();
               if exceeds (SOME(!solutions),try)
                 then raise Done
               else ())
        fun search () = AbsMachineSbt.solve
                          ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                           scInit)
    in
      if not (boundEq (try, SOME(0)))
        then (CSManager.reset ();
              (* solve query if bound > 0 *)
               (TimeLimit.timeLimit (!Global.timeLimit)
               (Timers.time Timers.solving search) ())
               handle Done => ()
               handle  TimeLimit.TimeOut =>
                 raise AbortQuery ("\n----------- TIME OUT ---------------\n" );
              (* printing is timed into solving! *)
              CSManager.reset ();           (* in case Done was raised *)
              (* check if number of solutions is correct *)
              checkSolutions (expected, try, !solutions))
      else if !Global.chatter >= 3
             then Msg.message ("Skipping query (bound = 0)\n")
           else if !Global.chatter >= 4
                  then Msg.message ("skipping")
                else ();
                  if !Global.chatter >= 3
                    then Msg.message "____________________________________________\n\n"
                  else if !Global.chatter >= 4
                         then Msg.message (" OK\n")
                       else ()
    end

  (* %query <expected> <try> A or %query <expected> <try> X : A  *)
  fun query args =
    case (!Compile.optimize) of
         (* Execute query where program clauses are
            indexed using substitution trees -- if we require the proof term X
            it will be reconstructed after the query A has succeeded - bp
          *)
      Compile.Indexing => querySbt args
    | Compile.LinearHeads => query' args
    | _ => query' args


 (* %querytabled <expected solutions> <max stages tried>  A
or  %querytabled <expected solutions> <max stages tried>  X : A
  note : %querytabled terminates if we have found the expected number of
  solutions or if we have reached the maximal number of stages *)
  fun querytabled ((numSol, try, quy), Paths.Loc (fileName, r)) =
    let
      val _ = if !Global.chatter >= 3
                then Msg.message ("%querytabled " ^ boundToString numSol ^ " " ^
                            boundToString try)
              else ()
      (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
      val (A, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r))
      (* times itself *)
      val _ = if !Global.chatter >= 4
                then Msg.message (" ")
              else ()
      val _ = if !Global.chatter >= 3
                then Msg.message ("\n" ^ (Timers.time Timers.printing expToString)
                            (IntSyn.Null, A) ^ ".\n")
              else ()
     (* Problem: we cannot give an answer substitution for the variables
        in the printed query, since the new variables in this query
        may not necessarily have global scope.

        For the moment, we print only the answer substitution for the
        original variables encountered during parsing.
     *)
     (* val Xs' = if !Global.chatter >= 3 then Names.namedEVars () else Xs *)
      val g = (Timers.time Timers.compiling Compile.compileGoal)
        (IntSyn.Null, A)

      (* solutions = ref <n> counts the number of solutions found *)
      val solutions = ref 0
      val status = ref false
      val solExists = ref false

      (* stage = ref <n> counts the number of stages found *)
      val stages = ref 1

      (* Initial success continuation prints substitution (according to chatter level)
         and raises exception Done if bound has been reached, otherwise it returns
         to search for further solutions
       *)
      fun scInit O =
        (solutions := !solutions+1;
         solExists := true ;
         if !Global.chatter >= 3
           then (Msg.message ("\n---------- Solutions " ^ Int.toString (!solutions) ^
                        " ----------\n");
                 Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ " \n"))
         else if !Global.chatter >= 1
                then Msg.message "."
              else ();

        (case optName
           of NONE => ()
         | SOME(name) => (Msg.message (CompSyn.pskeletonToString O ^ "\n");
                          (Timers.time Timers.ptrecon PtRecon.solve)
                              (O, (g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                               (fn (O, M) =>
                                if !Global.chatter >= 3
                                  then Msg.message ((Timers.time Timers.printing evarInstToString)
                                              [(M, name)] ^ "\n")
                                else ()))));

      (if !Global.chatter >= 3 then
         (* Question: should we collect constraints in M? *)
         case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs of
           NONE => ()
         | SOME(str) =>
             Msg.message ("Remaining constraints:\n"
                    ^ str ^ "\n")
       else ());
       (if !Global.chatter >= 1 then Msg.message "More solutions?\n" else ());
       case numSol of
         NONE => ()
       | SOME n => (if (!solutions = n)
                    then
                      ((if !Global.chatter >= 1
                        then Msg.message "Found enough solutions\n"
                        else ());
                       raise Done)
                    else ())
           )

      (* loops -- scinit will raise exception Done *)
      fun loop () =  (if exceeds (SOME(!stages-1),try)
                      then ((if !Global.chatter >= 1
                             then Msg.message
                                      ("\n ================= " ^
                                       " Number of tries exceeds stages " ^
                                       " ======================= \n")
                             else ());
                            status := false;
                            raise Done)
                      else ();
                      (if !Global.chatter >= 1
                       then Msg.message
                                ("\n ====================== Stage " ^
                                 Int.toString(!stages) ^
                                 " finished =================== \n")
                       else ());
                      if exceeds (SOME(!stages),try)
                      then (Msg.message ("\n ================= " ^
                                         " Number of tries exceeds stages " ^
                                         " ======================= \n");
                            status := false;
                            raise Done)
                      else ();
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
      val _ = Tabled.fillTable ()
      fun tabledSearch () =
        (Tabled.solve((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null),
                      scInit) ;
         CSManager.reset ();    (* in case Done was raised *)
         (* next stage until table doesn't change *)
         loop ();
         checkStages (try, !stages))

    in
      if not (boundEq (try, SOME(0)))
        then (CSManager.reset ();
              (* solve query if bound > 0 *)
              (TimeLimit.timeLimit (!Global.timeLimit)
               (Timers.time Timers.solving tabledSearch) ())
              handle TimeLimit.TimeOut =>
               (Msg.message "\n----------- TIME OUT ---------------\n" ; raise Done))

          handle Done => ()
      else if !Global.chatter >= 3
             then Msg.message ("Skipping query (bound = 0)\n")
           else if !Global.chatter >= 2
                  then Msg.message ("skipping")
                else ();
      if !Global.chatter >= 3
        then
          (Msg.message "\n____________________________________________\n\n";
           Msg.message ("number of stages: tried "    ^ boundToString try ^ " \n" ^
                  "terminated after " ^ Int.toString (!stages) ^ " stages \n \n");
           if (!solExists) then ()
            else Msg.message "\nNO solution exists to query \n\n";
           if (!status) then
             Msg.message "Tabled evaluation COMPLETE \n \n"
           else
             Msg.message "Tabled evaluation NOT COMPLETE \n \n";
           Msg.message "\n____________________________________________\n\n";
           Msg.message "\n Table Indexing parameters: \n";
           case (!TableParam.strategy) of
              TableParam.Variant =>  Msg.message "\n       Table Strategy := Variant \n"
            | TableParam.Subsumption => Msg.message "\n       Table Strategy := Subsumption \n";
            if (!TableParam.strengthen)
              then
                Msg.message "\n       Strengthening := true \n"
            else
              Msg.message "\n       Strengthening := false \n";

            Msg.message ("\nNumber of table indices : " ^
                   Int.toString(Tabled.tableSize()) ^ "\n");

            Msg.message ("Number of suspended goals : " ^
                   Int.toString(Tabled.suspGoalNo()) ^ "\n");

            Msg.message "\n____________________________________________\n\n")
      else (if !Global.chatter >= 3
             then Msg.message (" OK\n")
           else ());
        Tabled.updateGlobalTable (g, !status)
    end



  (* Interactive Query Top Level *)

  fun qLoop () = qLoops (CSManager.reset ();
                         Parser.parseTerminalQ ("?- ", "   ")) (* primary, secondary prompt *)
  and qLoops (s) = qLoops' ((Timers.time Timers.parsing S.expose) s)
  and qLoops' (S.Empty) = true          (* normal exit *)
    | qLoops' (S.Cons (query, s')) =
      let
        val (A, optName, Xs) = ReconQuery.queryToQuery(query, Paths.Loc ("stdIn", Paths.Reg (0,0)))
                                        (* times itself *)
        val g = (Timers.time Timers.compiling Compile.compileGoal)
                    (IntSyn.Null, A)
        fun scInit M =
            ((if !Global.chatter >= 1
              then Msg.message ((Timers.time Timers.printing evarInstToString)
                                    Xs ^ "\n")
              else ());
             case optName
               of NONE => ()
                | SOME(name) =>
                  if !Global.chatter >= 3
                    then Msg.message ((Timers.time Timers.printing evarInstToString)
                                       [(M, name)] ^ "\n")
                  else ();
             if !Global.chatter >= 3
               (* Question: should we collect constraints from M *)
               then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                      of NONE => ()
                       | SOME(str) =>
                         Msg.message ("Remaining constraints:\n"
                                ^ str ^ "\n")
             else ();
             if moreSolutions () then () else raise Done)
        val _ = if !Global.chatter >= 3
                  then Msg.message "Solving...\n"
                else ()
      in
        ((Timers.time Timers.solving AbsMachine.solve)
         ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit); (* scInit is timed into solving! *)
         Msg.message "No more solutions\n")
        handle Done => ();
        (* Ignore s': parse one query at a time *)
        qLoop ()
      end


  (* querytabled interactive top loop *)
  fun qLoopT () = qLoopsT (CSManager.reset ();
                         Parser.parseTerminalQ ("?- ", "   ")) (* primary, secondary prompt *)
  and qLoopsT (s) = qLoopsT' ((Timers.time Timers.parsing S.expose) s)
  and qLoopsT' (S.Empty) = true         (* normal exit *)
    | qLoopsT' (S.Cons (query, s')) =
      let
        val solExists = ref false
        val (A, optName, Xs) = ReconQuery.queryToQuery(query, Paths.Loc ("stdIn", Paths.Reg (0,0)))
                                        (* times itself *)
        val g = (Timers.time Timers.compiling Compile.compileGoal)
                    (IntSyn.Null, A)
        val _ = Tabled.reset ()
        fun scInit O =
            ((if !Global.chatter >= 1
              then Msg.message ((Timers.time Timers.printing evarInstToString) Xs ^ "\n")
              else ());
             case optName
               of NONE => ()
                | SOME(name) =>
                  if !Global.chatter >= 3
                    then Msg.message (" Sorry cannot reconstruct pskeleton proof terms yet \n")
                  else ();
             if !Global.chatter >= 3
               (* Question: should we collect constraints from M? *)
               then case (Timers.time Timers.printing Print.evarCnstrsToStringOpt) Xs
                      of NONE => ()
                       | SOME(str) =>
                         Msg.message ("Remaining constraints:\n"
                                ^ str ^ "\n")
             else ();
             solExists := true;
             if moreSolutions () then () else raise Done)
        (* loops -- scinit will raise exception Done *)
        fun loop () =  (if Tabled.nextStage () then
                          loop ()
                       else
                        (* table did not change,
                         * i.e. all solutions have been found
                         * we check for *all* solutions
                         *)
                         raise Completed)
        val _ = if !Global.chatter >= 3
                  then Msg.message "Solving...\n"
                else ()
      in
        ((Timers.time Timers.solving Tabled.solve)
         ((g,IntSyn.id), CompSyn.DProg (IntSyn.Null, IntSyn.Null), scInit); (* scInit is timed into solving! *)
         (loop()
          handle Completed =>
            if !solExists then
              Msg.message "No more solutions\n"
            else
              Msg.message "the query has no solution\n"))
        handle Done => ();
        (* Ignore s': parse one query at a time *)
        qLoopT ()
      end

end; (* functor Solve *)
