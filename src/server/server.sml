signature SERVER =
sig

  val server : string * string list -> OS.Process.status

end  (* signature SERVER *)

functor Server
  (structure SigINT : SIGINT
   structure Timing : TIMING
   structure Lexer : LEXER
   structure Twelf : TWELF)
  :> SERVER =
struct

  val globalConfig : Twelf.Config.config option ref = ref NONE

  (* readLine () = (command, args)
     reads a command and and its arguments from the command line.
  *)
  fun readLine () =
      let
        val line = TextIO.inputLine (TextIO.stdIn)
        fun triml ss = Substring.dropl Char.isSpace ss
        fun trimr ss = Substring.dropr Char.isSpace ss
        val line' = triml (trimr (Substring.all line))
      in
	if Substring.size (line') = 0
        then readLine ()
        else
          let
            val (command', args') = Substring.position " " line'
          in
            (Substring.string command',
             Substring.string (triml args'))
	  end
      end
  
  (* tokenize (args) = [token1, token2, ..., tokenn]
     splits the arguments string into a list of space-separated
     tokens
  *)
  fun tokenize (args) = String.tokens Char.isSpace args

  (* exception Error for server errors *)
  exception Error of string
  fun error (msg) = raise Error(msg)

  fun quote (string) = "`" ^ string ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  fun issue (Twelf.OK) = print ("%% OK %%\n")
    | issue (Twelf.ABORT) = print ("%% ABORT %%\n")

  (* Checking if there are no extraneous arguments *)
  fun checkEmpty ("") = ()
    | checkEmpty (args) = error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  fun getFile ("", default) = default
    | getFile (fileName, default) = fileName

  (* File names, not defaults *)
  fun getFile' ("") = error "Missing filename"
    | getFile' (fileName) = fileName

  (* Identifiers, used as a constant *)
  fun getId (id::nil) = id
    | getId (nil) = error "Missing identifier"
    | getId (ts) = error "Extraneous arguments"

  (* Identifiers, used as a trace specification *)
  fun getIds (ids) = ids

  (* Strategies for %prove, %establish *)
  fun getStrategy ("FRS"::nil) = Twelf.Prover.FRS
    | getStrategy ("RFS"::nil) = Twelf.Prover.RFS
    | getStrategy (nil) = error "Missing strategy"
    | getStrategy (t::nil) = error (quote t ^ " is not a strategy (must be FRS or RFS)")
    | getStrategy (ts) = error "Extraneous arguments"

  fun strategyToString (Twelf.Prover.FRS) = "FRS"
    | strategyToString (Twelf.Prover.RFS) = "RFS"

  (* Booleans *)
  fun getBool ("true"::nil) = true
    | getBool ("false"::nil) = false
    | getBool (nil) = error "Missing boolean value"
    | getBool (t::nil) = error (quote t ^ " is not a boolean")
    | getBool (ts) = error "Extraneous arguments"

  (* Natural numbers *)
  fun getNat (t::nil) =
        (Lexer.stringToNat t
	 handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number"))
    | getNat (nil) = error "Missing natural number"
    | getNat (ts) = error "Extraneous arguments"

  (* Limits ( *, or natural number) *)
  fun getLimit ("*"::nil) = NONE
    | getLimit (t::ts) = SOME (getNat (t::ts))
    | getLimit (nil) = error "Missing `*' or natural number"

  fun limitToString (NONE) = "*"
    | limitToString (SOME(i)) = Int.toString i

  (* Tabling strategy *)
  fun getTableStrategy ("Variant"::nil) = Twelf.Table.Variant
    | getTableStrategy ("Subsumption"::nil) = Twelf.Table.Subsumption
    | getTableStrategy (nil) = error "Missing tabling strategy"
    | getTableStrategy (t::nil) = error (quote t ^ " is not a tabling strategy (must be Variant or Subsumption)")
    | getTableStrategy (ts) = error "Extraneous arguments"

  fun tableStrategyToString (Twelf.Table.Variant) = "Variant"
    | tableStrategyToString (Twelf.Table.Subsumption) = "Subsumption"

  (* Setting Twelf parameters *)
  fun setParm ("chatter"::ts) = Twelf.chatter := getNat ts
    | setParm ("doubleCheck"::ts) = Twelf.doubleCheck := getBool ts
    | setParm ("unsafe"::ts) = Twelf.unsafe := getBool ts
    | setParm ("Print.implicit"::ts) = Twelf.Print.implicit := getBool ts
    | setParm ("Print.depth"::ts) = Twelf.Print.depth := getLimit ts
    | setParm ("Print.length"::ts) = Twelf.Print.length := getLimit ts
    | setParm ("Print.indent"::ts) = Twelf.Print.indent := getNat ts
    | setParm ("Print.width"::ts) = Twelf.Print.width := getNat ts
    | setParm ("Trace.detail"::ts) = Twelf.Trace.detail := getNat ts
    | setParm ("Compile.optimize"::ts) = Twelf.Compile.optimize := getBool ts
    | setParm ("Prover.strategy"::ts) = Twelf.Prover.strategy := getStrategy ts
    | setParm ("Prover.maxSplit"::ts) = Twelf.Prover.maxSplit := getNat ts
    | setParm ("Prover.maxRecurse"::ts) = Twelf.Prover.maxRecurse := getNat ts
    | setParm ("Table.strategy"::ts) = Twelf.Table.strategy := getTableStrategy ts
    | setParm ("Table.strengthen"::ts) = Twelf.Table.strengthen := getBool ts
    | setParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | setParm (nil) = error ("Missing parameter")

  (* Getting Twelf parameter values *)
  fun getParm ("chatter"::ts) = Int.toString (!Twelf.chatter)
    | getParm ("doubleCheck"::ts) = Bool.toString (!Twelf.doubleCheck)
    | getParm ("unsafe"::ts) = Bool.toString (!Twelf.unsafe)
    | getParm ("Print.implicit"::ts) = Bool.toString (!Twelf.Print.implicit)
    | getParm ("Print.depth"::ts) = limitToString (!Twelf.Print.depth)
    | getParm ("Print.length"::ts) = limitToString (!Twelf.Print.length)
    | getParm ("Print.indent"::ts) = Int.toString (!Twelf.Print.indent)
    | getParm ("Print.width"::ts) = Int.toString (!Twelf.Print.width)
    | getParm ("Trace.detail"::ts) = Int.toString (!Twelf.Trace.detail)
    | getParm ("Compile.optimize"::ts) = Bool.toString (!Twelf.Compile.optimize)
    | getParm ("Prover.strategy"::ts) = strategyToString (!Twelf.Prover.strategy)
    | getParm ("Prover.maxSplit"::ts) = Int.toString (!Twelf.Prover.maxSplit)
    | getParm ("Prover.maxRecurse"::ts) = Int.toString (!Twelf.Prover.maxRecurse)
    | getParm ("Table.strategy"::ts) = tableStrategyToString (!Twelf.Table.strategy)
    | getParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | getParm (nil) = error ("Missing parameter")

  (* serve' (command, args) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
  fun serve' ("set", args) =
      (setParm (tokenize args); serve (Twelf.OK))
    | serve' ("get", args) =
      (print (getParm (tokenize args) ^ "\n");
       serve (Twelf.OK))

    | serve' ("Print.sgn", args) =
      (checkEmpty args; Twelf.Print.sgn (); serve (Twelf.OK))
    | serve' ("Print.prog", args) =
      (checkEmpty args; Twelf.Print.prog (); serve (Twelf.OK))
    | serve' ("Print.subord", args) =
      (checkEmpty args; Twelf.Print.subord (); serve (Twelf.OK))
    | serve' ("Print.TeX.sgn", args) =
      (checkEmpty args; Twelf.Print.TeX.sgn (); serve (Twelf.OK))
    | serve' ("Print.TeX.prog", args) =
      (checkEmpty args; Twelf.Print.TeX.prog (); serve (Twelf.OK))
    (*
      serve' ("toc", args) = error "NYI"
    | serve' ("list-program", args) = error "NYI"
    | serve' ("list-signature", args) = error "NYI"
    *)
    (* | serve' ("type-at", args) = error "NYI" *)
    (* | serve' ("complete-at", args) = error "NYI" *)

    | serve' ("Trace.trace", args) =
      (Twelf.Trace.trace (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | serve' ("Trace.traceAll", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.All);
       serve (Twelf.OK))
    | serve' ("Trace.untrace", args) =
      (checkEmpty args; Twelf.Trace.trace (Twelf.Trace.None);
       serve (Twelf.OK))

    | serve' ("Trace.break", args) =
      (Twelf.Trace.break (Twelf.Trace.Some (getIds (tokenize args)));
       serve (Twelf.OK))
    | serve' ("Trace.breakAll", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.All);
       serve (Twelf.OK))
    | serve' ("Trace.unbreak", args) =
      (checkEmpty args; Twelf.Trace.break (Twelf.Trace.None);
       serve (Twelf.OK))

    | serve' ("Trace.show", args) =
      (checkEmpty args; Twelf.Trace.show ();
       serve (Twelf.OK))
    | serve' ("Trace.reset", args) =
      (checkEmpty args; Twelf.Trace.reset ();
       serve (Twelf.OK))

    | serve' ("Timers.show", args) =
      (checkEmpty args; Timers.show (); serve (Twelf.OK))
    | serve' ("Timers.reset", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))
    | serve' ("Timers.check", args) =
      (checkEmpty args; Timers.reset (); serve (Twelf.OK))

    | serve' ("OS.chDir", args) =
      (Twelf.OS.chDir (getFile' args); serve (Twelf.OK))
    | serve' ("OS.getDir", args) =
      (checkEmpty args; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK))
    | serve' ("OS.exit", args) =
      (checkEmpty args; ())

    | serve' ("quit", args) = ()		(* quit, as a concession *)

    | serve' ("Config.read", args) =
      let
	val fileName = getFile (args, "sources.cfg")
      in
	globalConfig := SOME (Twelf.Config.read fileName);
	serve (Twelf.OK)
      end
    | serve' ("Config.load", args) =
      (case !globalConfig
	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.load (valOf (!globalConfig))))
    | serve' ("make", args) =
      let
	val fileName = getFile (args, "sources.cfg")
      in
	globalConfig := SOME (Twelf.Config.read fileName);
	serve (Twelf.Config.load (valOf (!globalConfig)))
      end

    | serve' ("reset", args) =
      (checkEmpty args; Twelf.reset (); serve (Twelf.OK))
    | serve' ("loadFile", args) =
        serve (Twelf.loadFile (getFile' args))
    | serve' ("readDecl", args) =
      (checkEmpty args; serve (Twelf.readDecl ()))
    | serve' ("decl", args) =
        serve (Twelf.decl (getId (tokenize args)))

    | serve' ("top", args) =
      (checkEmpty args;
       Twelf.top ();
       serve (Twelf.OK))

    | serve' ("Table.top", args) =
      (checkEmpty args;
       Twelf.Table.top ();
       serve (Twelf.OK))

    | serve' (t, args) =
         error ("Unrecognized command " ^ quote t)

  and serveLine () = serve' (readLine ())

  and serve (Twelf.OK) = (issue (Twelf.OK); serveLine ())
    | serve (Twelf.ABORT) = (issue (Twelf.ABORT); serveLine ())

  fun serveTop (status) =
      serve (status)
      handle Error (msg) => (print ("Server error: " ^ msg ^ "\n");
			     serveTop (Twelf.ABORT))
	   | exn => (print ("Uncaught exception: " ^ exnMessage exn ^ "\n");
		     serveTop (Twelf.ABORT))

  fun server (name, _) =
      (* ignore server name and arguments *)
      (print (Twelf.version ^ "\n");
       Timing.init ();			(* initialize timers *)
       SigINT.interruptLoop (fn () => serveTop (Twelf.OK));
       OS.Process.success)

end;  (* functor Server *)

structure Server =
  Server (structure SigINT = SigINT
	  structure Timing = Timing
	  structure Lexer = Lexer
	  structure Twelf = Twelf);
