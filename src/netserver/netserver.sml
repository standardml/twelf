signature NETSERVER =
sig

    (* int argument is which port number to run on *)

    val flashServer : int -> unit (* Macromedia Flash XMLSocket interface *)
    val humanServer : int -> unit (* Human-readable interface, suitable for telnet *)
    (* second argument is what directory server.html is kept in *)
    val httpServer : int -> string -> unit (* HTTP interface, suitable for javascript XMLHttpRequest *)
    val setExamplesDir : string -> unit (* filesystem directory where twelf examples are kept *)
end  (* signature SERVER *)

functor NetServer
	    (structure Timing : TIMING
	     structure Twelf : TWELF
	     structure Msg : MSG)
	    :> NETSERVER =
struct

fun join delim [] = ""
  | join delim [x] = x
  | join delim (h::tl) = h ^ delim ^ (join delim tl)

type server = { send : string -> unit,
		exec : string -> unit }

type protocol = { init: unit -> unit,
		  reset: unit -> unit,
		  recv: server -> string -> unit, 
		  send: server -> string -> unit,
		  done: unit -> unit }

structure S = Socket

val maxConnections = 128 (* queue size for waiting connections in listen *)
                         (* below --- set to some arbitrary high value. *)

(* fun loop f state = loop f (f state) *)
fun loop f  = (f (); loop f)

fun vec2str v = String.implode 
		    (map (Char.chr o Word8.toInt)
				    (Word8Vector.foldr op:: nil v))
fun str2vec l = Word8Vector.fromList
			 (map (Word8.fromInt o Char.ord)
			      (String.explode l))

fun fileText fname = 
    let
	val s = TextIO.openIn fname
	val txt = TextIO.inputAll s
	val _ = TextIO.closeIn s
    in
	txt
    end

fun fileData fname = 
    let
	val s = BinIO.openIn fname
	val data = BinIO.inputAll s
	val _ = BinIO.closeIn s
    in
	vec2str data
    end

exception EOF
exception Quit

fun send conn str = (Compat.SocketIO.sendVec(conn, str2vec str); ())

local
    structure SS = Substring
in
fun parseCmd s = 
    let
	val (c,a) = SS.position " " (Compat.Substring.full s)
    in
	(SS.string c, SS.string (SS.dropl Char.isSpace a))
    end
end

fun quote (string) = "`" ^ string ^ "'"

val examplesDir : string option ref = ref NONE
fun setExamplesDir s = examplesDir := SOME s

(* exception Error for server errors *)
exception Error of string
fun error (msg) = raise Error(msg)

fun serveExample e =
	if (case e of
		"ccc" => true
	      | "cut-elim" => true
	      | "handbook" => true
	      | "lp-horn" => true
	      | "prop-calc" => true
	      | "units" => true
	      | "church-rosser" => true
	      | "fj" => true
	      | "incll" => true
	      | "mini-ml" => true
	      | "small-step" => true
	      | "alloc-sem" => true
	      | "compile" => true
	      | "fol" => true
	      | "kolm" => true
	      | "modal" => true
	      | "tabled" => true
	      | "arith" => true
	      | "cpsocc" => true
	      | "guide" => true
	      | "lp" => true
	      | "polylam" => true
	      | "tapl-ch13" => true
	      | _ => false)
	then ((OS.FileSys.chDir (Option.valOf(!examplesDir) ^ "/" ^ e); Twelf.make "sources.cfg") 
	      handle e => raise Error ("Exception " ^ exnName e ^ " raised."))
	else (raise Error ("Unknown example " ^ quote e))
	     
(* Natural numbers *)
fun getNat (t::nil) =
    (Lexer.stringToNat t
     handle Lexer.NotDigit (char) => error (quote t ^ " is not a natural number"))
  | getNat (nil) = error "Missing natural number"
  | getNat (ts) = error "Extraneous arguments"

(* Example specifiers *)
fun getExample (t::nil) = t
  | getExample (nil) = error "Missing example"
  | getExample (ts) = error "Extraneous arguments"

(* Setting Twelf parameters *)
fun setParm ("chatter"::ts) = Twelf.chatter := getNat ts
  | setParm (t::ts) = error ("Unknown parameter " ^ quote t)
  | setParm (nil) = error ("Missing parameter")
		    
fun exec' conn ("quit", args) = (Msg.message "goodbye.\n"; raise Quit)
  | exec' conn ("set", args) = (setParm (String.tokens Char.isSpace args); Twelf.OK) 
  | exec' conn ("readDecl", args) = Twelf.loadString args
  | exec' conn ("decl", args) = Twelf.decl args
  | exec' conn ("example", args) = serveExample (getExample (String.tokens Char.isSpace args))
  | exec' conn (t, args) = raise Error ("Unrecognized command " ^ quote t)

fun exec conn str = (case exec' conn (parseCmd str) 
			  handle Error s => (Msg.message ("Server Error: " ^ s ^ "\n"); Twelf.ABORT)
		      of
			 Twelf.OK => Msg.message "%%% OK %%%\n"
		       | Twelf.ABORT => Msg.message "%%% ABORT %%%\n")
		    
		    
fun stripcr s = Substring.string (Substring.dropr (fn x => x = #"\r") (Compat.Substring.full s))

fun flashProto() = 
    let 
	val buf : string ref = ref ""
	fun isnull #"\000" = true
	  | isnull _ = false
	fun recv (u : server) s = 
	    let
		val _ = buf := !buf ^ s
		val (rem::cmds) = rev(String.fields isnull (!buf))
		val _ = app (#exec u) (rev cmds)
	    in
		buf := rem
	    end
	fun send (u : server) s = (#send u) (s ^ "\000")
    in
	{
	 init = (fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n")),
	 reset = (fn () => buf := ""),
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

fun humanProto() = 
    let 
	val buf : string ref = ref ""
	fun isnewl #"\n" = true
	  | isnewl #"\r" = false
	  | isnewl _ = false
	fun recv (u : server) s = 
	    let
		val _ = buf := !buf ^ s
		val (rem::cmds) = rev(String.fields isnewl (!buf))
		val _ = app (#exec u) (map stripcr (rev cmds))
	    in
		buf := rem
	    end
	fun send (u : server) s = (#send u) ("> " ^ s)
    in
	{
	 init = (fn () =>  Msg.message (Twelf.version ^ "\n%%% OK %%%\n")),
	 reset = (fn () => buf := ""),
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

fun httpProto dir =
    let 
	val ibuf : string ref = ref ""
	val obuf : string ref = ref ""
	val parsingHeaders = ref true
	val contentLength = ref 0
	val method : string ref = ref ""
	val url : string ref = ref ""
	val headers : string list ref = ref []
	fun isnewl #"\n" = true
	  | isnewl _ = false

	fun handlePostRequest (u : server) =
	    let
		val shouldQuit = ((#exec u) (!ibuf); false) handle Quit => true
		val response = !obuf
		val clmsg = "Content-Length: " ^ Int.toString (size response) ^ "\n"
	    in
		#send u ("HTTP/1.1 200 OK\nContent-Type: text/plain\n" ^ clmsg ^ "\n");
		#send u response;
		if shouldQuit then raise Quit else raise EOF
	    end 
	fun handleGetRequest (u : server) =
	    let
		val ok = "200 OK"
		val missing = "404 Not Found"
		val (content, ctype, rcode) = (case !url of
                             "/" => (fileText (dir ^ "/server.html"), "application/xhtml+xml", ok)
			   | "/server.js" => (fileText (dir ^ "/server.js"), "text/plain", ok)
			   | "/server.css" => (fileText (dir ^ "/server.css"), "text/css", ok)
			   | "/grad.png" => (fileData (dir ^ "/grad.png"), "image/png", ok)
			   | "/twelfguy.png" => (fileData (dir ^ "/twelfguy.png"), "image/png", ok)
			   | "/input.png" => (fileData (dir ^ "/input.png"), "image/png", ok)
			   | "/output.png" => (fileData (dir ^ "/output.png"), "image/png", ok)
			   | "/floral.png" => (fileData (dir ^ "/floral.png"), "image/png", ok)
			   | _ => ("Error 404", "text/plain", missing))
					      
		val clmsg = "Content-Length: " ^ Int.toString (size content) ^ "\r\n"
		val ctmsg = "Content-Type: " ^ ctype ^ "\r\n"
		val resp = "HTTP/1.1 " ^ rcode ^ "\r\n"
	    in
		#send u (resp ^ ctmsg  ^ clmsg ^ "\r\n");
		#send u content;
		raise EOF;
		()
	    end 
	fun handleRequest (u : server) = 
	    if !method = "GET" then handleGetRequest u
	    else if !method = "POST" then handlePostRequest u
	    else #send u "HTTP/1.1 500 Server Error\n\n"
	fun headerExec s = headers := (s :: !headers)
	fun recvContent u = (if (size (!ibuf) >= !contentLength) then handleRequest u else ())
	fun parseHeaders() = 
	    (let
		 val (request::headers) = rev (!headers)
		 val [m, u, httpVersion] = String.tokens (fn x => x = #" ") request
		 val _ = method := m
		 val _ = url := u
		 fun getField s = 
		     let
			 val (k::v) = String.fields (fn x => x = #":") s
			 val v = join ":" v
		     in
			 (k, substring(v, 1, (size v) - 1)) end
		 fun proc_one s = 
		     let
			 val (k, v) = getField s 
		     in 
			 if k = "Content-Length" then contentLength := (case Int.fromString v of NONE => 0 | SOME n => n) else ()
		     end
		 val () = app proc_one headers
	     in
		 parsingHeaders := false
	     end handle Bind => raise EOF)
		
	fun interp (u : server) [] = raise Match
	  | interp u [x] = ibuf := x
	  | interp u (h::tl) = 
	    let
		val sch = stripcr h
	    in
		if sch = "" 
		then (ibuf := join "\n" tl; parseHeaders(); recvContent u)
		else (headerExec (stripcr h); interp u tl)
	    end
	fun recv (u : server) s = 
	    (ibuf := !ibuf ^ s;
	     if !parsingHeaders 
	     then interp u (String.fields isnewl (!ibuf))
	     else recvContent u)
	fun send (u : server) s = obuf := !obuf ^ s
	fun reset () = (parsingHeaders := true; ibuf := ""; obuf := ""; contentLength := 0; headers := []; url := ""; method := "")
    in
	{
	 init = (fn () => ()),
	 reset = reset,
	 send = send,
	 recv = recv,
	 done = (fn () => ())
	 }
    end

fun protoServer (proto : protocol) portNum =
    let
	val sock = INetSock.TCP.socket()
	val _ = S.Ctl.setREUSEADDR (sock, true)
	val _ = S.bind (sock, INetSock.any portNum)
	val _ = S.listen (sock, maxConnections)

	fun read_one conn u () =
	    let
		val v = S.recvVec(conn, 1024) (* arbitrary buffer size *)
	    in
		if Word8Vector.length v = 0 
		then raise EOF
		else (#recv proto) u (vec2str v)
	    end
	fun accept_one () = 
	    let
		val (conn, addr) = S.accept sock
		val _ = (#reset proto) ()
		val u = {send = send conn, exec = exec conn}
		val _ = Msg.setMessageFunc ((#send proto) u)
		val _ = (#init proto) ()
	    in
		loop (read_one conn u) handle EOF => ((#done proto)(); S.close conn)
					    | Quit => ((#done proto)(); S.close conn; raise Quit)
	    end
    in
	loop accept_one handle Quit => S.close sock
    end

fun flashServer port = protoServer (flashProto()) port
fun humanServer port = protoServer (humanProto()) port
fun httpServer port dir = protoServer (httpProto dir) port

end

structure NetServer =
NetServer (structure Timing = Timing
	   structure Twelf = Twelf
	   structure Msg = Msg);

