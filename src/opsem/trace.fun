functor Trace (structure IntSyn' : INTSYN
	       structure Names : NAMES
		 sharing Names.IntSyn = IntSyn'
	       structure Whnf : WHNF
		 sharing Whnf.IntSyn = IntSyn'
	       structure Abstract : ABSTRACT
		 sharing Abstract.IntSyn = IntSyn'
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

    (* Printing Utilities *)

    fun headToString (G, I.Const (c)) = N.constName c
      | headToString (G, I.BVar(k)) = N.bvarName (G, k)
    fun expToString (GU) = P.expToString (GU) ^ ". "
    fun decToString (GD) = P.decToString (GD) ^ ". "
    fun eqnToString (E) = P.eqnToString (E) ^ ". "

    fun newline () = print "\n"

    fun printCtx (I.Null) = print "No hypotheses or parameters\n"
      | printCtx (I.Decl(I.Null, D)) =
          (print (decToString (I.Null, D));
	   newline ())
      | printCtx (I.Decl(G, D)) =
	  (printCtx (G);
	   print (decToString (G, D));
	   newline ())

    fun evarsToString (Xnames) =
        let
	  val inst = P.evarInstToString (Xnames)
	  val constrOpt = P.evarConstrToStringOpt (Xnames)
	in
	  case constrOpt
	    of NONE => inst
	     | SOME(constr) => inst ^ "\nConstraints:\n" ^ constr
	end

    fun varsToEVarInst (nil) = nil
      | varsToEVarInst (name::names) =
        case N.getEVarOpt name
	  of NONE => (print ("Trace warning: ignoring unknown variable " ^ name ^ "\n");
		      varsToEVarInst (names))
           | SOME(X) => (X,name)::varsToEVarInst (names)

    fun printVars (names) = print (evarsToString (varsToEVarInst names))

    fun printVarstring (line) =
          printVars (List.tl (String.tokens Char.isSpace line))

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

    val detail = ref 1

    fun setDetail (NONE) = print ("Trace warning: detail is not a valid integer\n")
      | setDetail (SOME(n)) =
        if 0 <= n (* andalso n <= 2 *)
	  then detail := n
	else print ("Trace warning: detail must be positive\n")

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
\d n - detail --- set trace detail to n (0, 1, or 2)\n\
\h - hypotheses --- show current hypotheses\n\
\g - goal --- show current goal\n\
\i - instantiation --- show instantiation of variables in current goal\n\
\v X1 ... Xn - variables --- show instantiation of X1 ... Xn\n\
\? for help"

    val currentGoal = ref (I.Uni (I.Type)) (* dummy initialization *)
    val currentEVarInst : (I.Exp * I.name) list ref = ref nil

    fun setEVarInst (Xs) =
        currentEVarInst := List.map (fn X => (X, N.evarName (I.Null, X))) Xs

    fun breakAction (G) =
        let
	  val _ = print " "
	  val line = TextIO.inputLine (TextIO.stdIn)
	in
	  case String.sub (line, 0)
	    of #"\n" => ()
	     | #"n" => (breakTSpec := All)
	     | #"r" => (breakTSpec := None)
	     | #"t" => (traceTSpec := All;
			print "% Now tracing all";
			breakAction (G))
	     | #"u" => (traceTSpec := None;
			print "% Now tracing none";
			breakAction (G))
	     | #"d" => (setDetail (Int.fromString (String.extract (line, 1, NONE)));
			print ("% Trace detail now " ^ Int.toString (!detail));
			breakAction (G))
	     | #"h" => (printCtx G; breakAction (G))
	     | #"g" => (print (expToString (G, !currentGoal));
			breakAction (G))
	     | #"i" => (print (evarsToString (List.rev (!currentEVarInst)));
			breakAction (G))
	     | #"v" => (printVarstring (line); breakAction (G))
	     | #"?" => (printHelp (); breakAction (G))
	     | _ => (print "unrecognized command (? for help)";
		     breakAction (G))
	end

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
      IntroHyp of IntSyn.Head * IntSyn.Dec
    | DischargeHyp of IntSyn.Head * IntSyn.Dec

    | IntroParm of IntSyn.Head * IntSyn.Dec
    | DischargeParm of IntSyn.Head * IntSyn.Dec

    | Resolved of IntSyn.Head * IntSyn.Head (* resolved with clause c, fam a *)
    | Subgoal of (IntSyn.Head * IntSyn.Head) * (unit -> int) (* clause c, fam a, nth subgoal *)

    | SolveGoal of goalTag * IntSyn.Head * IntSyn.Exp
    | RetryGoal of goalTag * (IntSyn.Head * IntSyn.Head) * IntSyn.Exp (* clause c failed, fam a *)
    | FailGoal of goalTag * IntSyn.Head * IntSyn.Exp

    | Unify of (IntSyn.Head * IntSyn.Head) * IntSyn.Exp * IntSyn.Exp (* clause head == goal *)
    | FailUnify of (IntSyn.Head * IntSyn.Head) * string	(* failure message *)
   
    fun eventToString (G, IntroHyp (_, D)) =
        "% Introducing hypothesis\n" ^ decToString (G, D)
      | eventToString (G, DischargeHyp (_, I.Dec (SOME(x), _))) =
	"% Discharging hypothesis " ^ x
      | eventToString (G, IntroParm (_, D)) =
	"% Introducing parameter\n" ^ decToString (G, D)
      | eventToString (G, DischargeParm (_, I.Dec (SOME(x), _))) =
	"% Discharging parameter " ^ x

      | eventToString (G, Resolved (Hc, Ha)) =
        "% Resolved with clause " ^ headToString (G, Hc) ^ "\n"
	^ evarsToString (List.rev (!currentEVarInst))
      | eventToString (G, Subgoal ((Hc, Ha), msg)) =
        "% Solving subgoal (" ^ Int.toString (msg ()) ^ ") of clause "
	^ headToString (G, Hc)

      | eventToString (G, SolveGoal (SOME(tag), _, V)) =
	"% Goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | eventToString (G, RetryGoal (SOME(tag), (Hc, Ha), V)) =
	"% Backtracking from clause " ^ headToString (G, Hc) ^ "\n"
	^ "% Retrying goal " ^ Int.toString tag ^ ":\n" ^ expToString (G, V)
      | eventToString (G, FailGoal (SOME(tag), _, V)) =
        "% Failed goal " ^ Int.toString tag

      | eventToString (G, Unify ((Hc, Ha), Q, P)) =
	"% Trying clause " ^ headToString (G, Hc) ^ "\n"
	^ eqnToString (I.Eqn (G, Q, P))
      | eventToString (G, FailUnify ((Hc, Ha), msg)) =
	"% Unification failed with clause " ^ headToString (G, Hc) ^ ":\n"
	^ msg

    fun traceEvent (G, e) = print (eventToString (G, e))

    fun setGoal (G, V) = 
        (currentGoal := V;
	 setEVarInst (Abstract.collectEVars (G, (V, I.id), nil)))

    fun monitorHead (cids, I.Const(c)) = List.exists (fn c' => c = c') cids
      | monitorHead (cids, I.BVar(k)) = false

    fun monitorHeads (cids, (Hc, Ha)) =
          monitorHead (cids, Hc) orelse monitorHead (cids, Ha)

    fun monitorEvent (cids, IntroHyp (H, _)) =
          monitorHead (cids, H)
      | monitorEvent (cids, DischargeHyp (H, _)) =
	  monitorHead (cids, H)
      | monitorEvent (cids, IntroParm (H, _)) =
          monitorHead (cids, H)
      | monitorEvent (cids, DischargeParm (H, _)) =
	  monitorHead (cids, H)

      | monitorEvent (cids, SolveGoal (_, H, V)) =
          monitorHead (cids, H)
      | monitorEvent (cids, RetryGoal (_, (Hc, Ha), _)) =
	  monitorHeads (cids, (Hc, Ha))
      | monitorEvent (cids, FailGoal (_, H, _)) =
	  monitorHead (cids, H)

      | monitorEvent (cids, Resolved (Hc, Ha)) =
	  monitorHeads (cids, (Hc, Ha))
      | monitorEvent (cids, Subgoal ((Hc, Ha), _)) = 
	  monitorHeads (cids, (Hc, Ha))

      | monitorEvent (cids, Unify ((Hc, Ha), _, _)) =
	  monitorHeads (cids, (Hc, Ha))
      | monitorEvent (cids, FailUnify ((Hc, Ha), _)) =
	  monitorHeads (cids, (Hc, Ha))

    fun monitorDetail (Unify _) = !detail >= 2
      | monitorDetail (FailUnify _) = !detail >= 2
      | monitorDetail _ = !detail >= 1

    (* expensive if tracing Unify! *)
    (* but: maintain only if break or trace is on *)
    (* may not be sufficient for some information *)
    fun maintain (G, SolveGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, RetryGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, FailGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, Unify (_, Q, P)) =
        (* show substitution for variables in clause head if tracing unification *)
        setEVarInst (Abstract.collectEVars (G, (P, I.id),
					    Abstract.collectEVars (G, (Q, I.id), nil)))
      | maintain _ = ()

    fun monitorBreak (None, G, e) = false
      | monitorBreak (Some (cids), G, e) =
        if monitorEvent (cids, e)
	  then (maintain (G, e); traceEvent (G, e); breakAction (G); true)
	else false
      | monitorBreak (All, G, e) =
	  (maintain (G, e); traceEvent (G, e); breakAction (G); true)

    fun monitorTrace (None, G, e) = false
      | monitorTrace (Some (cids), G, e) =
        if monitorEvent (cids, e)
	  then (maintain (G, e); traceEvent (G, e); newline (); true)
	else false
      | monitorTrace (All, G, e) =
	  (maintain (G, e); traceEvent (G, e); newline (); true)

    fun signal (G, e) =
        if monitorDetail (e)
	  then if monitorBreak (!breakTSpec, G, e) (* stops, continues after input *)
		 then ()
	       else (monitorTrace (!traceTSpec, G, e); ()) (* prints trace, continues *)
	else ()

    fun showSpec (msg, None) = print (msg ^ " = None\n")
      | showSpec (msg, Some(names)) =
        (print (msg ^ " = Some [");
	 List.app (fn name => print (" " ^ name)) names;
	 print "]\n")
      | showSpec (msg, All) = print (msg ^ " = All\n")

    fun show () =
        (showSpec ("trace", !traceSpec);
	 showSpec ("break", !breakSpec);
	 print ("detail = " ^ Int.toString (!detail) ^ "\n"))

    fun reset () = (trace (None); break (None); detail := 1)
  end

end;  (* functor Trace *)
