functor Trace (structure IntSyn' : INTSYN
	       structure Names : NAMES
		 sharing Names.IntSyn = IntSyn'
	       structure Whnf : WHNF
		 sharing Whnf.IntSyn = IntSyn'
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

    (* Collecting EVars *)
    (* copied and edited from abstract.fun *)
    (* K is a list of pairs (X, "X") *)

    fun eqEVar (I.EVar(r,_,_,_)) (I.EVar(r',_,_,_), _) = (r = r')

    (* collectExpW (G, (U, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- U : V      (U,s) in whnf
       No circularities in U
       and   K' = K, K''
	     where K'' contains all EVars and FVars in (U,s)
    *)
    fun collectExpW (G, (I.Uni L, s), K) = K
      | collectExpW (G, (I.Pi ((D, _), V), s), K) =
          collectExp (I.Decl (G, I.decSub (D, s)), (V, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (I.Root (_ , S), s), K) =
	  collectSpine (G, (S, s), K)
      | collectExpW (G, (I.Lam (D, U), s), K) =
	  collectExp (I.Decl (G, I.decSub (D, s)), (U, I.dot1 s), collectDec (G, (D, s), K))
      | collectExpW (G, (X as I.EVar (r, GX, V, Cnstr), s), K) =
	  if List.exists (eqEVar X) K
	    then collectSub(G, s, K)
	  else  (* N.evarName will assign name if none exists *)
	    collectSub(G, s, (X, N.evarName (G, X))::collectExp (GX, (V, I.id), K))
      (* No other cases can occur due to whnf invariant *)

    (* collectExp (G, (U, s), K) = K' 
       
       same as collectExpW  but  (U,s) need not to be in whnf 
    *) 
    and collectExp (G, Us, K) = collectExpW (G, Whnf.whnf Us, K)

    (* collectSpine (G, (S, s), K) = K' 

       Invariant: 
       If    G |- s : G1     G1 |- S : V > P
       then  K' = K, K''
       where K'' contains all EVars and FVars in (S, s)
     *)
    and collectSpine (G, (I.Nil, _), K) = K
      | collectSpine (G, (I.SClo(S, s'), s), K) = 
          collectSpine (G, (S, I.comp (s', s)), K)
      | collectSpine (G, (I.App (U, S), s), K) =
	  collectSpine (G, (S, s), collectExp (G, (U, s), K))

    (* collectDec (G, (x:V, s), K) = K'

       Invariant: 
       If    G |- s : G1     G1 |- V : L
       then  K' = K, K''
       where K'' contains all EVars and FVars in (V, s)
    *)
    and collectDec (G, (I.Dec (_, V), s), K) =
          collectExp (G, (V, s), K)

    (* collectSub (G, s, K) = K' 

       Invariant: 
       If    G |- s : G1    
       then  K' = K, K''
       where K'' contains all EVars and FVars in s
    *)
    and collectSub (G, I.Shift _, K) = K
      | collectSub (G, I.Dot (I.Idx _, s), K) = collectSub (G, s, K)
      | collectSub (G, I.Dot (I.Exp (U), s), K) =
	  collectSub (G, s, collectExp (G, (U, I.id), K))

    (* Printing Utilities *)

    fun headToString (G, I.Const (c)) = N.constName c
      | headToString (G, I.BVar(k)) = N.bvarName (G, k)
    fun expToString (GU) = P.expToString (GU) ^ ". "
    fun decToString (GD) = P.decToString (GD) ^ ". "
    fun eqnToString (E) = P.eqnToString (E) ^ ". "

    fun printExp (GU) = print (P.expToString GU)

    fun newline () = print "\n"

    fun printCtx (I.Null) = print "No hypotheses or parameters\n"
      | printCtx (I.Decl(I.Null, D)) =
          (print (decToString (I.Null, D));
	   newline ())
      | printCtx (I.Decl(G, D)) =
	  (printCtx (G);
	   print (decToString (G, D));
	   newline ())

    fun varsToEVarInst (nil) = nil
      | varsToEVarInst (name::names) =
        case N.getEVarOpt name
	  of NONE => (print ("Trace warning: ignoring unknown variable " ^ name ^ "\n");
		      varsToEVarInst (names))
           | SOME(X) => (X,name)::varsToEVarInst (names)

    fun printVars (names) = print (P.evarInstToString (varsToEVarInst names))

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

    val level = ref 1

    fun setLevel (NONE) = print ("Trace warning: level is not a valid integer\n")
      | setLevel (SOME(n)) =
        if 0 <= n (* andalso n <= 2 *)
	  then level := n
	else print ("Trace warning: level must be positive\n")

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
\l n - level --- set trace level to n (0, 1, or 2)\n\
\h - hypotheses --- show current hypotheses\n\
\g - goal --- show current goal\n\
\i - instantiation --- show instantiation of variables in current goal\n\
\v X1 ... Xn - variables --- show instantiation of X1 ... Xn\n\
\? for help"

    val currentGoal = ref (I.Uni (I.Type)) (* dummy initialization *)
    val currentEVarInst : (I.Exp * I.name) list ref = ref nil

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
	     | #"l" => (setLevel (Int.fromString (String.extract (line, 1, NONE)));
			print ("% Trace level now " ^ Int.toString (!level));
			breakAction (G))
	     | #"h" => (printCtx G; breakAction (G))
	     | #"g" => (printExp (G, !currentGoal); breakAction (G))
	     | #"i" => (print (P.evarInstToString (List.rev (!currentEVarInst)));
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
    | FailUnify of IntSyn.Head * IntSyn.Head
   
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
	^ P.evarInstToString (List.rev (!currentEVarInst))
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
      | eventToString (G, FailUnify (Hc, Ha)) =
	"% Unification failed with clause " ^ headToString (G, Hc)

    fun traceEvent (G, e) = print (eventToString (G, e))

    fun setGoal (G, V) = 
        (currentGoal := V;
	 currentEVarInst := collectExp (G, (V, I.id), nil))

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
      | monitorEvent (cids, FailUnify (Hc, Ha)) =
	  monitorHeads (cids, (Hc, Ha))

    fun monitorLevel (Unify _) = !level >= 2
      | monitorLevel (FailUnify _) = !level >= 2
      | monitorLevel _ = !level >= 1

    (* expensive if tracing Unify! *)
    (* but: maintain only if break or trace is on *)
    (* may not be sufficient for some information *)
    fun maintain (G, SolveGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, RetryGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, FailGoal (_, _, V)) = setGoal (G, V)
      | maintain (G, Unify (_, Q, P)) =
        (* show substitution for variables in clause head if tracing unification *)
        (currentEVarInst := collectExp (G, (P, I.id), collectExp (G, (Q, I.id), nil)))
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
        if monitorLevel (e)
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

    fun status () =
        (print ("level = " ^ Int.toString (!level) ^ "\n");
	 showSpec ("trace", !traceSpec);
	 showSpec ("break", !breakSpec))

    fun reset () = (level := 1; trace (None); break (None))
  end

end;  (* functor Trace *)
