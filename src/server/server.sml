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

  (* readLine () = [token1,...,tokenn]
     reads a non-empty list of tokens from standard input.
     Tokens are separated by whitespace.
  *)
  fun readLine () =
      let
	val line = TextIO.inputLine (TextIO.stdIn)
	val tokens = String.tokens Char.isSpace line
      in
	case tokens
	  of nil => readLine ()
	   | _ => tokens
      end

  (* exception Error for server errors *)
  exception Error of string
  fun error (msg) = raise Error(msg)

  fun quote (string) = "`" ^ string ^ "'"

  (* Print the OK or ABORT messages which are parsed by Emacs *)
  fun issue (Twelf.OK) = print ("%% OK %%\n")
    | issue (Twelf.ABORT) = print ("%% ABORT %%\n")

  (* Checking if there are no extraneous arguments *)
  fun checkEmpty (nil) = ()
    | checkEmpty (t::ts) = error "Extraneous arguments"

  (* Command argument types *)
  (* File names, given a default *)
  fun getFile (fileName::nil, default) = fileName
    | getFile (nil, default) = default
    | getFile (ts, default) = error "Extraneous arguments"

  (* File names, not defaults *)
  fun getFile' (fileName::nil) = fileName
    | getFile' (nil) = error "Missing filename"
    | getFile' (ts) = error "Extraneous arguments"

  (* Identifiers, used as a constant *)
  fun getId (id::nil) = id
    | getId (nil) = error "Missing identifier"
    | getId (ts) = error "Extraneous arguments"

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

  (* Setting Twelf parameters *)
  fun setParm ("chatter"::ts) = Twelf.chatter := getNat ts
    | setParm ("doubleCheck"::ts) = Twelf.doubleCheck := getBool ts
    | setParm ("Print.implicit"::ts) = Twelf.Print.implicit := getBool ts
    | setParm ("Print.depth"::ts) = Twelf.Print.depth := getLimit ts
    | setParm ("Print.length"::ts) = Twelf.Print.length := getLimit ts
    | setParm ("Print.indent"::ts) = Twelf.Print.indent := getNat ts
    | setParm ("Print.width"::ts) = Twelf.Print.width := getNat ts
    | setParm ("Compile.optimize"::ts) = Twelf.Compile.optimize := getBool ts
    | setParm ("Prover.strategy"::ts) = Twelf.Prover.strategy := getStrategy ts
    | setParm ("Prover.maxSplit"::ts) = Twelf.Prover.maxSplit := getNat ts
    | setParm ("Prover.maxRecurse"::ts) = Twelf.Prover.maxRecurse := getNat ts
    | setParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | setParm (nil) = error ("Missing parameter")

  (* Getting Twelf parameter values *)
  fun getParm ("chatter"::ts) = Int.toString (!Twelf.chatter)
    | getParm ("doubleCheck"::ts) = Bool.toString (!Twelf.doubleCheck)
    | getParm ("Print.implicit"::ts) = Bool.toString (!Twelf.Print.implicit)
    | getParm ("Print.depth"::ts) = limitToString (!Twelf.Print.depth)
    | getParm ("Print.length"::ts) = limitToString (!Twelf.Print.length)
    | getParm ("Print.indent"::ts) = Int.toString (!Twelf.Print.indent)
    | getParm ("Print.width"::ts) = Int.toString (!Twelf.Print.width)
    | getParm ("Compile.optimize"::ts) = Bool.toString (!Twelf.Compile.optimize)
    | getParm ("Prover.strategy"::ts) = strategyToString (!Twelf.Prover.strategy)
    | getParm ("Prover.maxSplit"::ts) = Int.toString (!Twelf.Prover.maxSplit)
    | getParm ("Prover.maxRecurse"::ts) = Int.toString (!Twelf.Prover.maxRecurse)
    | getParm (t::ts) = error ("Unknown parameter " ^ quote t)
    | getParm (nil) = error ("Missing parameter")

  (* serve' (tokens) = ()
     executes the server commands represented by `tokens', 
     issues success or failure and then reads another command line.
     Invariant: tokens must be non-empty.

     All input for one command must be on the same line.
  *)
  fun serve' ("set"::ts) =
      (setParm ts; serve (Twelf.OK))
    | serve' ("get"::ts) =
      (print (getParm ts ^ "\n"); serve (Twelf.OK))

    (*
      serve' ("toc"::ts) = error "NYI"
    | serve' ("list-program"::ts) = error "NYI"
    | serve' ("list-signature"::ts) = error "NYI"
    *)
    (* | serve' ("type-at"::ts) = error "NYI" *)
    (* | serve' ("complete-at"::ts) = error "NYI" *)

    | serve' ("Timers.show"::ts) = (checkEmpty ts; Timers.show (); serve (Twelf.OK))
    | serve' ("Timers.reset"::ts) = (checkEmpty ts; Timers.reset (); serve (Twelf.OK))
    | serve' ("Timers.check"::ts) = (checkEmpty ts; Timers.reset (); serve (Twelf.OK))

    | serve' ("OS.chDir"::ts) =
      (Twelf.OS.chDir (getFile' ts); serve (Twelf.OK))
    | serve' ("OS.getDir"::ts) =
      (checkEmpty ts; print (Twelf.OS.getDir () ^ "\n"); serve (Twelf.OK))
    | serve' ("OS.exit"::ts) =
      (checkEmpty ts; ())

    | serve' ("quit"::ts) = ()		(* quit, as a concession *)

    | serve' ("Config.read"::ts) =
      let
	val fileName = getFile (ts, "sources.cfg")
      in
	globalConfig := SOME (Twelf.Config.read fileName);
	serve (Twelf.OK)
      end
    | serve' ("Config.load"::ts) =
      (case !globalConfig
	 of NONE => (globalConfig := SOME (Twelf.Config.read "sources.cfg"))
          | _ => ();
       serve (Twelf.Config.load (valOf (!globalConfig))))

    | serve' ("reset"::ts) =
      (checkEmpty ts; Twelf.reset (); serve (Twelf.OK))
    | serve' ("loadFile"::ts) =
        serve (Twelf.loadFile (getFile' ts))
    | serve' ("readDecl"::ts) =
      (checkEmpty ts; serve (Twelf.readDecl ()))
    | serve' ("decl"::ts) =
        serve (Twelf.decl (getId ts))

    | serve' ("top"::ts) =
      (checkEmpty ts;
       Twelf.top ();
       serve (Twelf.OK))

    | serve' (t::ts) =
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
