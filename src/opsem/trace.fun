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

    fun newline () = print "\n"

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
	   of NONE => (print ("Warning: ignoring undeclared constant " ^ name ^ "\n");
		       toCids names)
            | SOME (cid) => cid::toCids names)

    fun initTrace (None) = traceTSpec := None
      | initTrace (Some (names)) = traceTSpec := Some (toCids names)
      | initTrace (All) = traceTSpec := All

    fun initBreak (None) = breakTSpec := None
      | initBreak (Some (names)) = breakTSpec := Some (toCids names)
      | initBreak (All) = breakTSpec := All

    fun printHelp () =
        print "<newline> - continue\n\
\n - next (step from here)\n\
\r - run\n\
\t - trace all\n\
\u - untrace all\n\
\? for help"

    fun breakAction () =
        (print " ";
	 case String.sub (TextIO.inputLine (TextIO.stdIn), 0)
	     of #"\n" => ()
	      | #"n" => (breakTSpec := All)
              | #"r" => (breakTSpec := None)
	      | #"t" => (traceTSpec := All; breakAction ())
	      | #"u" => (traceTSpec := None; breakAction ())
	      | #"?" => (printHelp (); breakAction ())
	      | _ => (print "unrecognized command (? for help)";
		      breakAction ()))

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
      AtomGoal of unit -> IntSyn.dctx * IntSyn.Exp
    | ImplGoal of unit -> IntSyn.dctx * IntSyn.Exp
    | AllGoal of unit -> IntSyn.dctx * IntSyn.Exp

    | IntroHyp of unit -> IntSyn.dctx * IntSyn.Dec
    | DischargeHyp of unit -> IntSyn.dctx * IntSyn.Dec

    | IntroParm of unit -> IntSyn.dctx * IntSyn.Dec
    | DischargeParm of unit -> IntSyn.dctx * IntSyn.Dec

    | Unify of unit -> IntSyn.Eqn (* goal == clause head *)
    | Resolved of IntSyn.dctx * IntSyn.Head (* resolved with clause H *)
    | Subgoal of IntSyn.dctx * IntSyn.Head * (unit -> int) (* nth subgoal of H : _ *)
    | IntroEVar of unit -> IntSyn.dctx * IntSyn.Exp * IntSyn.Exp (* X : V *)

    | SolveGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)
    | RetryGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)
    | FailGoal of goalTag * IntSyn.Head * (unit -> IntSyn.dctx * IntSyn.Exp)

    | TryClause of unit -> IntSyn.dctx * IntSyn.Head
    | FailClauseShallow of unit -> IntSyn.dctx * IntSyn.Head
    | FailClauseDeep of unit -> IntSyn.dctx * IntSyn.Head 
   
    fun eventToString (IntroHyp (msg)) =
        "% Introducing hypothesis\n" ^ decToString (msg ())
      | eventToString (DischargeHyp (msg)) =
        (case msg ()
	   of (G, I.Dec(SOME(x), _)) => "% Discharging hypothesis " ^ x)
      | eventToString (IntroParm (msg)) =
	"% Introducing parameter\n" ^ decToString (msg ())
      | eventToString (DischargeParm (msg)) =
	(case msg ()
	   of (G, I.Dec(SOME(x), _)) => "% Discharging parameter " ^ x)

      | eventToString (Resolved (G, H)) =
        "% Resolved with clause " ^ headToString (G, H)
      | eventToString (Subgoal (G, H, msg)) =
        "% Solving subgoal number (" ^ Int.toString (msg ()) ^ ") of clause "
	^ headToString (G, H)

      | eventToString (SolveGoal (SOME(tag), _, msg)) =
	"% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (msg ())
      | eventToString (RetryGoal (SOME(tag), _, msg)) =
	"% Retrying goal " ^ Int.toString tag ^ ":\n" ^ expToString (msg ())
      | eventToString (FailGoal (SOME(tag), _, msg)) =
        "% Failed goal " ^ Int.toString tag

    fun traceEvent (e) = print (eventToString (e))

    fun monitorHead (cids, I.Const(c)) = List.exists (fn c' => c = c') cids
      | monitorHead (cids, I.BVar(k)) = false

    fun monitorEvent (cids, SolveGoal (_, H, msg)) =
          monitorHead (cids, H)
      | monitorEvent (cids, RetryGoal (_, H, msg)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, FailGoal (_, H, msg)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, Resolved (G, H)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, Subgoal (G, H, msg)) = 
	  monitorHead (cids, H)
      | monitorEvent _ = false

    fun monitorBreak (None, e) = false
      | monitorBreak (Some (cids), e) =
        if monitorEvent (cids, e)
	  then (traceEvent e; breakAction (); true)
	else false
      | monitorBreak (All, e) =
	(traceEvent e; breakAction (); true)

    fun monitorTrace (None, e) = ()
      | monitorTrace (Some (cids), e) =
        if monitorEvent (cids, e) then (traceEvent e; newline ()) else ()
      | monitorTrace (All, e) = (traceEvent e; newline ())

    fun signal (e) =
        if monitorBreak (!breakTSpec, e)
	  then ()
	else monitorTrace (!traceTSpec, e)

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
