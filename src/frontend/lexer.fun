(* Lexer *)
(* Author: Frank Pfenning *)

functor Lexer (structure Stream' : STREAM
               structure Paths' : PATHS)
  : LEXER =
struct

  structure Stream = Stream'
  structure Paths = Paths'

  datatype IdCase =
      Upper				(* [A-Z]<id> or _<id> *)
    | Lower				(* any other <id> *)
    | Quoted				(* '<id>', currently unused *)

  datatype Token =
      EOF				(* end of file or stream, also `%.' *)
    | DOT				(* `.' *)
    | COLON				(* `:' *)
    | LPAREN | RPAREN			(* `(' `)' *)
    | LBRACKET | RBRACKET		(* `[' `]' *)
    | LBRACE | RBRACE			(* `{' `}' *)
    | BACKARROW | ARROW			(* `<-' `->' *)
    | TYPE				(* `type' *)
    | EQUAL				(* `=' *)
    | ID of IdCase * string		(* identifer *)
    | UNDERSCORE			(* `_' *)
    | INFIX | PREFIX | POSTFIX		(* `%infix' `%prefix' `%postfix' *)
    | NAME				(* `%name' *)
    | SOLVE				(* `%solve' *)
    | QUERY	  			(* `%query' *)
    | MODE				(* `%mode' *)
    | TERMINATES			(* `%terminates' *)
    | THEOREM                           (* `%theorem' *)
    | PROVE                             (* `%prove' *)

  exception Error of string

  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  (* isSym (c) = B iff c is a legal symbolic identifier constituent *)
  (* excludes quote character and digits, which are treated specially *)
  (* Char.contains stages its computation *)
  val isSym : char -> bool = Char.contains "_!&$^+/<=>?@~|#*`;,-\\"

  (* isQuote (c) = B iff c is the quote character *)
  fun isQuote (c) = (c = #"'")

  (* isIdChar (c) = B iff c is legal identifier constituent *)
  fun isIdChar (c) = Char.isLower(c) orelse Char.isUpper (c)
                     orelse Char.isDigit (c) orelse isSym(c)
		     orelse isQuote (c)

  (* stringToToken (idCase, string, region) = (token, region)
     converts special identifiers into tokens, returns ID token otherwise
  *)
  fun stringToToken (Lower, "<-", r) = (BACKARROW, r)
    | stringToToken (Lower, "->", r) = (ARROW, r)
    | stringToToken (Upper, "_", r) = (UNDERSCORE, r)
    | stringToToken (Lower, "=", r) = (EQUAL, r)
    | stringToToken (Lower, "type", r) = (TYPE, r)
    | stringToToken (idCase, s, r) = (ID(idCase,s), r)

  (* lex (inputFun) = (token, region) stream

     inputFun maintains state, reading input one line at a time and
     returning a string terminated by <newline> each time.
     The end of the stream is signalled by a string consisting only of ^D
  *)
  fun lex (inputFun:Paths.pos -> string) =
  let
    local (* local state maintained by the lexer *)
      val s = ref ""			(* current string (line) *)
      and left = ref 0			(* position of first character in s *)
      and right = ref 0			(* position after last character in s *)
      val _ = Paths.resetLines ()	(* initialize line counter *)

      (* neither lexer nor parser should ever try to look beyond EOF *)
      val EOFString = String.str #"\^D"

      (* readNext () = ()
         Effect: read the next line, updating s, left, and right

         readNext relies on the invariant that identifiers are never
         spread across lines
      *)
      fun readNext () =
	  let
	    val nextLine = inputFun (!right)
	    val nextSize = String.size (nextLine)
	  in
	    if nextSize = 0		(* end of file? *)
	      then (s := EOFString;	(* fake EOF character string *)
		    left := !right;
		    right := !right + 1)
	    else (s := nextLine;
		  left := !right;
		  right := !right + nextSize;
		  Paths.newLine (!left)) (* remember new line position *)
	  end
    in
      (* char (i) = character at position i
         Invariant: i >= !left
	 Effects: will read input if i >= !right
      *)
      fun char (i) =
	  if i >= !right then (readNext (); char (i))
	  else String.sub (!s, i - !left)

      (* string (i,j) = substring at region including i, excluding j
         Invariant: i >= !left and i < j and j < !right
                    Note that the relevant parts must already have been read!
	 Effects: None
      *)
      fun string (i,j) = String.substring (!s, i - !left, j-i)
    end

    (* The remaining functions do not access the state or *)
    (* stream directly, using only functions char and string *)

    fun idToToken (idCase, (i,j)) = stringToToken (idCase, string (i,j), (i,j))

    (* Quote characters are part of the name *)
    (* Treat quoted identifiers as lowercase, since they no longer *)
    (* override infix state.  Quoted identifiers are now only used *)
    (* inside pragmas *)
    fun qidToToken (i,j) = (ID(Lower, string(i,j+1)), (i,j+1))

    (* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
    fun lexInitial (#":", i) = (COLON, (i-1,i))
      | lexInitial (#".", i) = (DOT, (i-1,i))
      | lexInitial (#"(", i) = (LPAREN, (i-1,i))
      | lexInitial (#")", i) = (RPAREN, (i-1,i))
      | lexInitial (#"[", i) = (LBRACKET, (i-1,i))
      | lexInitial (#"]", i) = (RBRACKET, (i-1,i))
      | lexInitial (#"{", i) = (LBRACE, (i-1,i))
      | lexInitial (#"}", i) = (RBRACE, (i-1,i))
      | lexInitial (#"%", i) = lexPercent (char(i), i+1)
      | lexInitial (#"_", i) = lexID (Upper,(i-1,i))
      | lexInitial (#"'", i) = lexID (Lower,(i-1,i)) (* lexQUID (i-1,i) *)
      | lexInitial (#"\^D", i) = (EOF, (i-1,i-1))
      | lexInitial (c, i) =
	if Char.isSpace (c) then lexInitial (char (i),i+1)
	else if Char.isUpper(c) then lexID (Upper, (i-1,i))
	else if Char.isDigit(c) then lexID (Lower, (i-1,i))
	else if Char.isLower(c) then lexID (Lower, (i-1,i))
	else if isSym(c) then lexID (Lower, (i-1,i))
	else error ((i-1,i), "Illegal character " ^ Char.toString (c))
        (* recover by ignoring: lexInitial (char(i), i+1) *)

    and lexID (idCase, (i,j)) =
        let fun lexID' (j) =
	        if isIdChar (char(j)) then lexID' (j+1)
		else idToToken (idCase, (i,j))
	in
	  lexID' (j)
	end

    (* lexQUID is currently not used --- no quoted identifiers *)
    and lexQUID (i,j) =
        if Char.isSpace (char(j))
	  then error ((i,j+1), "Whitespace in quoted identifier")
	       (* recover by adding implicit quote? *)
	       (* qidToToken (i, j) *)
	else if isQuote (char(j)) then qidToToken (i,j)
	     else lexQUID (i, j+1)

    and lexPercent (#".", i) = (EOF, (i-2,i))
      | lexPercent (#"{", i) = lexPercentBrace (char(i), i+1)
      | lexPercent (#"%", i) = lexComment (#"%", i)
      | lexPercent (c, i) =
        if isIdChar(c) then lexPragmaKey (lexID (Quoted, (i-1,i)))
	else if Char.isSpace(c) then lexComment (c, i)
	  else error ((i-1, i), "Comment character `%' not followed by white space")

    and lexPragmaKey (ID(_, "infix"), r) = (INFIX, r)
      | lexPragmaKey (ID(_, "prefix"), r) = (PREFIX, r)
      | lexPragmaKey (ID(_, "postfix"), r) = (POSTFIX, r)
      | lexPragmaKey (ID(_, "mode"), r) = (MODE, r)
      | lexPragmaKey (ID(_, "terminates"), r) = (TERMINATES, r)
      | lexPragmaKey (ID(_, "theorem"), r) = (THEOREM, r)
      | lexPragmaKey (ID(_, "prove"), r) = (PROVE, r)
      | lexPragmaKey (ID(_, "name"), r) = (NAME, r)
      | lexPragmaKey (ID(_, "solve"), r) = (SOLVE, r)
      | lexPragmaKey (ID(_, "query"), r) = (QUERY, r)
      | lexPragmaKey (ID(_, s), r) =
        error (r, "Unknown keyword %" ^ s ^ " (single line comment starts with `%<whitespace>' or `%%')")
      (* comments are now started by %<whitespace> *)
      (*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)

    and lexComment (#"\n", i) = lexInitial (char(i), i+1)
      | lexComment (#"%", i) = lexCommentPercent (char(i), i+1)
      | lexComment (#"\^D", i) =
          error ((i-1, i-1), "Unclosed single-line comment at end of file")
	  (* recover: (EOF, (i-1,i-1)) *)
      | lexComment (c, i) = lexComment (char(i), i+1)

    and lexCommentPercent (#".", i) = (EOF, (i-2, i))
      | lexCommentPercent (c, i) = lexComment (c, i)

    and lexPercentBrace (c, i) = lexDComment (c, 1, i)

    (* functions lexing delimited comments below take nesting level l *)
    and lexDComment (#"}", l, i) = lexDCommentRBrace (char(i), l, i+1)
      | lexDComment (#"%", l, i) = lexDCommentPercent (char(i), l, i+1)
      | lexDComment (#"\^D", l, i) =
          (* pass comment beginning for error message? *)
          error ((i-1,i-1), "Unclosed delimited comment at end of file")
	  (* recover: (EOF, (i-1,i-1)) *)
      | lexDComment (c, l, i) = lexDComment (char(i), l, i+1)

    and lexDCommentPercent (#"{", l, i) = lexDComment (char(i), l+1, i+1)
      | lexDCommentPercent (#".", l, i) =
          error ((i-2, i), "Unclosed delimited comment at end of file token `%.'")
          (* recover: (EOF, (i-2,i)) *)
      | lexDCommentPercent (c, l, i) = lexDComment (c, l, i)

    and lexDCommentRBrace (#"%", 1, i) = lexInitial (char(i), i+1)
      | lexDCommentRBrace (#"%", l, i) = lexDComment (char(i), l-1, i+1)
      | lexDCommentRBrace (c, l, i) = lexDComment (c, l, i)

    fun lexContinue (j) = Stream.delay (fn () => lexContinue' (j))
    and lexContinue' (j) = lexContinue'' (lexInitial (char(j), j+1))

    and lexContinue'' (mt as (token, (i,j))) =
          Stream.Cons (mt, lexContinue (j))
  in
    lexContinue (0)
  end  (* fun lex (inputFun) = let ... in ... end *)

  fun lexStream (instream) = lex (fn i => TextIO.inputLine (instream))

  fun lexTerminal (prompt0, prompt1) =
        lex (fn 0 => (print (prompt0) ;
		      TextIO.inputLine (TextIO.stdIn))
	      | i => (print (prompt1) ;
		      TextIO.inputLine (TextIO.stdIn)))

  fun toString' (DOT) = "."
    | toString' (COLON) = ":"
    | toString' (LPAREN) = "("
    | toString' (RPAREN) = ")"
    | toString' (LBRACKET) = "["
    | toString' (RBRACKET) = "]"
    | toString' (LBRACE) = "{"
    | toString' (RBRACE) = "}"
    | toString' (BACKARROW) = "<-"
    | toString' (ARROW) = "->"
    | toString' (TYPE) = "type"
    | toString' (EQUAL) = "="
    | toString' (UNDERSCORE) = "_"
    | toString' (INFIX) = "%infix"
    | toString' (PREFIX) = "%prefix"
    | toString' (POSTFIX) = "%postfix"
    | toString' (NAME) = "%name"
    | toString' (SOLVE) = "%solve"
    | toString' (QUERY) = "%query"
    | toString' (MODE) = "%mode"
    | toString' (TERMINATES) = "%terminates"
    | toString' (THEOREM) = "%theorem"
    | toString' (PROVE) = "%prove"

 fun toString (ID(_,s)) = "identifier `" ^ s ^ "'"
   | toString (EOF) = "end of file or `%.'"
   | toString (token) = "`" ^ toString' token ^ "'"

 exception NotDigit of char

 (* charToNat(c) = n converts character c to decimal equivalent *)
 (* raises NotDigit(c) if c is not a digit 0-9 *)
 fun charToNat (c) =
     let val digit = Char.ord(c) - Char.ord(#"0")
     in
       if digit < 0 orelse digit > 9
	 then raise NotDigit (c)
       else digit
     end

 (* stringToNat(s) = n converts string s to a natural number *)
 (* raises NotDigit(c) if s contains character c which is not a digit *)
 fun stringToNat (s) =
     let val l = String.size s
         fun stn (i, n) =
	     if i = l then n
	     else stn (i+1, 10 * n + charToNat (String.sub (s, i)))
     in
       stn (0, 0)
     end

  (* isUpper (s) = true, if s is a string starting with an uppercase
     letter or underscore (_).
  *)
  fun isUpper ("") = false
    | isUpper (s) =
      let val c = String.sub (s, 0)
       in
	 Char.isUpper c orelse c = #"_"
      end

end;  (* functor Lexer *)
