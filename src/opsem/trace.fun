functor Trace (structure IntSyn' : INTSYN
	       structure Names : NAMES
		 sharing Names.IntSyn = IntSyn'
	       structure Print : PRINT
		 sharing Print.IntSyn = IntSyn')
  : TRACE =
struct

  structure IntSyn = IntSyn'

  local
    structure I = IntSyn
    structure P = Print
    structure N = Names

  in

    fun headToString (G, I.Const (c)) = N.constName c
      | headToString (G, I.BVar(k)) = N.bvarName (G, k)
    fun expToString (GU) = P.expToString (GU) ^ ". "
    fun decToString (GD) = P.decToString (GD) ^ ". "
    fun printExp (GU) = print (P.expToString GU)

    fun newline () = print "\n"

    fun printCtx (I.Null) = print "--- no hypotheses or parameters ---\n"
      | printCtx (I.Decl(I.Null, D)) =
          (print (decToString (I.Null, D));
	   newline ())
      | printCtx (I.Decl(G, D)) =
	  (printCtx (G);
	   print (decToString (G, D));
	   newline ())

    datatype 'a Spec =
        None
      | Some of 'a list
      | All

    val traceSpec : string Spec ref = ref None
    val breakSpec : string Spec ref = ref None

    fun trace (None) = traceSpec := None
      | trace (Some (names)) = traceSpec := Some (names)
      | trace (All) = traceSpec := All

    fun break (None) = breakSpec := None
      | break (Some (names)) = breakSpec := Some (names)
      | break (All) = breakSpec := All

    val traceTSpec : I.cid Spec ref = ref None
    val breakTSpec : I.cid Spec ref = ref None

    fun toCids (nil) = nil
      | toCids (name::names) =
        (case N.nameLookup name
	   of NONE => (print ("Trace warning: ignoring undeclared constant " ^ name ^ "\n");
		       toCids names)
            | SOME (cid) => cid::toCids names)

    fun initTrace (None) = traceTSpec := None
      | initTrace (Some (names)) = traceTSpec := Some (toCids names)
      | initTrace (All) = traceTSpec := All

    fun initBreak (None) = breakTSpec := None
      | initBreak (Some (names)) = breakTSpec := Some (toCids names)
      | initBreak (All) = breakTSpec := All

    fun printHelp () =
        print
"<newline> - continue --- execute with current settings\n\
\n - next --- take a single step\n\
\r - run --- remove all breakpoints and continue\n\
\t - trace --- trace all events\n\
\u - untrace --- trace no events\n\
\h - hypotheses --- show current hypotheses\n\
\g - goal --- show current goal\n\
\? for help"

    val currentGoal = ref (I.Uni (I.Type)) (* dummy initialization *)

    fun breakAction (G) =
        (print " ";
	 case String.sub (TextIO.inputLine (TextIO.stdIn), 0)
	     of #"\n" => ()
	      | #"n" => (breakTSpec := All)
              | #"r" => (breakTSpec := None)
	      | #"t" => (traceTSpec := All;
			 print "% Now tracing all";
			 breakAction (G))
	      | #"u" => (traceTSpec := None;
			 print "% Now tracing none";
			 breakAction (G))
	      | #"h" => (printCtx G; breakAction (G))
              | #"g" => (printExp (G, !currentGoal); breakAction (G))
	      | #"?" => (printHelp (); breakAction (G))
	      | _ => (print "unrecognized command (? for help)";
		      breakAction (G)))

    type goalTag = int option

    val tag : goalTag ref = ref NONE
    fun tagGoal () =
        case !tag
	  of NONE => NONE
	   | SOME(n) => (tag := SOME(n+1); !tag)

    fun initTag () =
        case (!traceTSpec,!breakTSpec)
	  of (None, None) => tag := NONE
           | _ => tag := SOME(0)

    fun init () =
        (initTrace (!traceSpec);
	 initBreak (!breakSpec);
	 initTag ())

    datatype Event =
      AtomGoal of IntSyn.Exp
    | ImplGoal of IntSyn.Exp
    | AllGoal of IntSyn.Exp

    | IntroHyp of IntSyn.Head * IntSyn.Dec
    | DischargeHyp of IntSyn.Head * IntSyn.Dec

    | IntroParm of IntSyn.Head * IntSyn.Dec
    | DischargeParm of IntSyn.Head * IntSyn.Dec

    | Unify of IntSyn.Exp * IntSyn.Exp	(* goal == clause head *)
    | Resolved of IntSyn.Head * IntSyn.Head (* resolved with clause c, fam a *)
    | Subgoal of (IntSyn.Head * IntSyn.Head) * (unit -> int) (* clause c, fam a, nth subgoal *)
    | IntroEVar of IntSyn.Exp

    | SolveGoal of goalTag * IntSyn.Head * IntSyn.Exp
    | RetryGoal of goalTag * IntSyn.Head * IntSyn.Exp
    | FailGoal of goalTag * IntSyn.Head * IntSyn.Exp

    | TryClause of IntSyn.Head
    | FailClauseShallow of IntSyn.Head
    | FailClauseDeep of IntSyn.Head 
   
    fun eventToString (G, IntroHyp (_, D)) =
        "% Introducing hypothesis\n" ^ decToString (G, D)
      | eventToString (G, DischargeHyp (_, I.Dec (SOME(x), _))) =
	"% Discharging hypothesis " ^ x
      | eventToString (G, IntroParm (_, D)) =
	"% Introducing parameter\n" ^ decToString (G, D)
      | eventToString (G, DischargeParm (_, I.Dec (SOME(x), _))) =
	"% Discharging parameter " ^ x

      | eventToString (G, Resolved (Hc, Ha)) =
        "% Resolved with clause " ^ headToString (G, Hc)
      | eventToString (G, Subgoal ((Hc, Ha), msg)) =
        "% Solving subgoal (" ^ Int.toString (msg ()) ^ ") of clause "
	^ headToString (G, Hc)

      | eventToString (G, SolveGoal (SOME(tag), _, V)) =
	"% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | eventToString (G, RetryGoal (SOME(tag), _, V)) =
	"% Retrying goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | eventToString (G, FailGoal (SOME(tag), _, V)) =
        "% Failed goal " ^ Int.toString tag

    fun traceEvent (G, e) = print (eventToString (G, e))

    fun monitorHead (cids, I.Const(c)) = List.exists (fn c' => c = c') cids
      | monitorHead (cids, I.BVar(k)) = false

    fun monitorEvent (cids, IntroHyp (H, _)) =
          monitorHead (cids, H)
      | monitorEvent (cids, DischargeHyp (H, _)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, IntroParm (H, _)) =
          monitorHead (cids, H)
      | monitorEvent (cids, DischargeParm (H, _)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, SolveGoal (_, H, _)) =
          monitorHead (cids, H)
      | monitorEvent (cids, RetryGoal (_, H, _)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, FailGoal (_, H, _)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, Resolved (Hc, Ha)) =
	  monitorHead (cids, Hc) orelse monitorHead (cids, Ha)
      | monitorEvent (cids, Subgoal ((Hc, Ha), _)) = 
	  monitorHead (cids, Hc) orelse monitorHead (cids, Ha)
      | monitorEvent _ = false

    fun maintain (G, SolveGoal (_, _, V)) = (currentGoal := V)
      | maintain (G, RetryGoal (_, _, V)) = (currentGoal := V)
      | maintain (G, FailGoal (_, _, V)) = (currentGoal := V)
      | maintain _ = ()

    fun monitorBreak (None, G, e) = false
      | monitorBreak (Some (cids), G, e) =
        if monitorEvent (cids, e)
	  then (traceEvent (G, e); breakAction (G); true)
	else false
      | monitorBreak (All, G, e) =
	(traceEvent (G, e); breakAction (G); true)

    fun monitorTrace (None, G, e) = ()
      | monitorTrace (Some (cids), G, e) =
        if monitorEvent (cids, e)
	  then (traceEvent (G, e); newline ()) 
	else ()
      | monitorTrace (All, G, e) = (traceEvent (G, e); newline ())

    fun signal (G, e) =
        (maintain (G, e);		(* maintain internal state *)
	 if monitorBreak (!breakTSpec, G, e)
	  then ()
	else monitorTrace (!traceTSpec, G, e))

    fun showSpec (msg, None) = print ("No " ^ msg ^ "\n")
      | showSpec (msg, Some(names)) =
        (print (msg);
	 List.app (fn name => print (" " ^ name)) names;
	 print "\n")
      | showSpec (msg, All) = print (msg ^ " all constants\n")

    fun status () =
        (showSpec ("Tracing", !traceSpec);
	 showSpec ("Breakpoints", !breakSpec))

    fun reset () = (trace (None); break (None))
  end

end;  (* functor Trace *)
