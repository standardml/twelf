(* Lexer *)
(* Author: Frank Pfenning *)
(* Modified: Brigitte Pientka *)

functor Lexer (structure Stream' : STREAM
               (*! structure Paths' : PATHS !*)
                 )
  : LEXER =
struct

  structure Stream = Stream'
  (*! structure Paths = Paths' !*)

  local
    structure P = Paths
  in

  datatype IdCase =
      Upper                             (* [A-Z]<id> or _<id> *)
    | Lower                             (* any other <id> *)
    | Quoted                            (* '<id>', currently unused *)

  datatype Token =
      EOF                               (* end of file or stream, also `%.' *)
    | DOT                               (* `.' *)
    | PATHSEP                           (* `.' between <id>s *)
    | COLON                             (* `:' *)
    | LPAREN | RPAREN                   (* `(' `)' *)
    | LBRACKET | RBRACKET               (* `[' `]' *)
    | LBRACE | RBRACE                   (* `{' `}' *)
    | BACKARROW | ARROW                 (* `<-' `->' *)
    | TYPE                              (* `type' *)
    | EQUAL                             (* `=' *)
    | ID of IdCase * string             (* identifer *)
    | UNDERSCORE                        (* `_' *)
    | INFIX | PREFIX | POSTFIX          (* `%infix' `%prefix' `%postfix' *)
    | NAME                              (* `%name' *)
    | DEFINE                            (* `%define' *) (* -rv 8/27/01 *)
    | SOLVE                             (* `%solve' *)
    | QUERY                             (* `%query' *)
    | FQUERY                            (* `%fquery' *)
    | COMPILE                           (* '%compile' *) (* -ABP 4/4/03 *)
    | QUERYTABLED                       (* `%querytabled *)
    | MODE                              (* `%mode' *)
    | UNIQUE                            (* `%unique' *) (* -fp 8/17/03 *)
    | COVERS                            (* `%covers' *) (* -fp 3/7/01 *)
    | TOTAL                             (* `%total' *) (* -fp 3/18/01 *)
    | TERMINATES                        (* `%terminates' *)
    | REDUCES                           (* `%reduces' *) (* -bp  6/05/99 *)
    | TABLED                            (* `%tabled' *)     (* -bp 11/20/01 *)
    | KEEPTABLE                         (* `%keepTable' *)  (* -bp 11/20/01 *)
    | THEOREM                           (* `%theorem' *)
    | BLOCK                             (* `%block' *) (* -cs 5/29/01 *)
    | WORLDS                            (* `%worlds' *)
    | PROVE                             (* `%prove' *)
    | ESTABLISH                         (* `%establish' *)
    | ASSERT                            (* `%assert' *)
    | ABBREV                            (* `%abbrev' *)
    | TRUSTME                           (* `%trustme' *) (* -fp 8/26/05 *)
    | FREEZE                            (* `%freeze' *)
    | THAW                              (* `%thaw' *)
    | SUBORD                            (* `%subord' *) (* -gaw 07/11/08 *)
    | DETERMINISTIC                     (* `%deterministic' *) (* -rv 11/27/01 *)
    | CLAUSE                            (* `%clause' *) (* -fp 8/9/02 *)
    | SIG                               (* `%sig' *)
    | STRUCT                            (* `%struct' *)
    | WHERE                             (* `%where' *)
    | INCLUDE                           (* `%include' *)
    | OPEN                              (* `%open' *)
    | USE                               (* `%use' *)
    | STRING of string                  (* string constants *)

  exception Error of string

  fun error (r, msg) = raise Error (P.wrap (r, msg))

  (* isSym (c) = B iff c is a legal symbolic identifier constituent *)
  (* excludes quote character and digits, which are treated specially *)
  (* Char.contains stages its computation *)
  val isSym : char -> bool = Char.contains "_!&$^+/<=>?@~|#*`;,-\\"

  (* isUFT8 (c) = assume that if a character is not ASCII it must be
     part of a UTF8 Unicode encoding.  Treat these as lowercase
     identifiers.  Somewhat of a hack until there is native Unicode
     string support. *)
  fun isUTF8 (c) = not (Char.isAscii c)

  (* isQuote (c) = B iff c is the quote character *)
  fun isQuote (c) = (c = #"'")

  (* isIdChar (c) = B iff c is legal identifier constituent *)
  fun isIdChar (c) = Char.isLower(c) orelse Char.isUpper (c)
                     orelse Char.isDigit (c) orelse isSym(c)
                     orelse isQuote (c) orelse isUTF8(c)

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
     Argument to inputFun is the character position.
  *)
  fun lex (inputFun:int -> string) =
  let
    local (* local state maintained by the lexer *)
      val s = ref ""                    (* current string (line) *)
      and left = ref 0                  (* position of first character in s *)
      and right = ref 0                 (* position after last character in s *)
      val _ = P.resetLines ()           (* initialize line counter *)

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
            if nextSize = 0             (* end of file? *)
              then (s := EOFString;     (* fake EOF character string *)
                    left := !right;
                    right := !right + 1)
            else (s := nextLine;
                  left := !right;
                  right := !right + nextSize;
                  P.newLine (!left)) (* remember new line position *)
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

    fun idToToken (idCase, P.Reg (i,j)) = stringToToken (idCase, string (i,j), P.Reg (i,j))

    (* Quote characters are part of the name *)
    (* Treat quoted identifiers as lowercase, since they no longer *)
    (* override infix state.  Quoted identifiers are now only used *)
    (* inside pragmas *)
    fun qidToToken (P.Reg (i,j)) = (ID(Lower, string(i,j+1)), P.Reg (i,j+1))

    (* The main lexing functions take a character c and the next
       input position i and return a token with its region
       The name convention is lexSSS, where SSS indicates the state
       of the lexer (e.g., what has been lexed so far).

       Lexing errors are currently fatal---some error recovery code is
       indicated in comments.
    *)
    fun lexInitial (#":", i) = (COLON, P.Reg (i-1,i))
      | lexInitial (#".", i) = (DOT, P.Reg (i-1,i))
      | lexInitial (#"(", i) = (LPAREN, P.Reg (i-1,i))
      | lexInitial (#")", i) = (RPAREN, P.Reg (i-1,i))
      | lexInitial (#"[", i) = (LBRACKET, P.Reg (i-1,i))
      | lexInitial (#"]", i) = (RBRACKET, P.Reg (i-1,i))
      | lexInitial (#"{", i) = (LBRACE, P.Reg (i-1,i))
      | lexInitial (#"}", i) = (RBRACE, P.Reg (i-1,i))
      | lexInitial (#"%", i) = lexPercent (char(i), i+1)
      | lexInitial (#"_", i) = lexID (Upper, P.Reg (i-1,i))
      | lexInitial (#"'", i) = lexID (Lower, P.Reg (i-1,i)) (* lexQUID (i-1,i) *)
      | lexInitial (#"\^D", i) = (EOF, P.Reg (i-1,i-1))
      | lexInitial (#"\"", i) = lexString (P.Reg(i-1, i))
      | lexInitial (c, i) =
        if Char.isSpace (c) then lexInitial (char (i),i+1)
        else if Char.isUpper(c) then lexID (Upper, P.Reg (i-1,i))
        else if Char.isDigit(c) then lexID (Lower, P.Reg (i-1,i))
        else if Char.isLower(c) then lexID (Lower, P.Reg (i-1,i))
        else if isSym(c) then lexID (Lower, P.Reg (i-1,i))
        else if isUTF8(c) then lexID (Lower, P.Reg (i-1,i))
        else error (P.Reg (i-1,i), "Illegal character " ^ Char.toString (c))
        (* recover by ignoring: lexInitial (char(i), i+1) *)

    and lexID (idCase, P.Reg (i,j)) =
        let fun lexID' (j) =
                if isIdChar (char(j)) then lexID' (j+1)
                else
                   idToToken (idCase, P.Reg (i,j))
        in
          lexID' (j)
        end

    (* lexQUID is currently not used --- no quoted identifiers *)
    and lexQUID (P.Reg (i,j)) =
        if Char.isSpace (char(j))
          then error (P.Reg (i,j+1), "Whitespace in quoted identifier")
               (* recover by adding implicit quote? *)
               (* qidToToken (i, j) *)
        else if isQuote (char(j)) then qidToToken (P.Reg (i,j))
             else lexQUID (P.Reg (i, j+1))

    and lexPercent (#".", i) = (EOF, P.Reg (i-2,i))
      | lexPercent (#"{", i) = lexPercentBrace (char(i), i+1)
      | lexPercent (#"%", i) = lexComment (#"%", i)
      | lexPercent (c, i) =
        if isIdChar(c) then lexPragmaKey (lexID (Quoted, P.Reg (i-1, i)))
        else if Char.isSpace(c) then lexComment (c, i)
          else error (P.Reg (i-1, i), "Comment character `%' not followed by white space")

    and lexPragmaKey (ID(_, "infix"), r) = (INFIX, r)
      | lexPragmaKey (ID(_, "prefix"), r) = (PREFIX, r)
      | lexPragmaKey (ID(_, "postfix"), r) = (POSTFIX, r)
      | lexPragmaKey (ID(_, "mode"), r) = (MODE, r)
      | lexPragmaKey (ID(_, "unique"), r) = (UNIQUE, r) (* -fp 8/17/03 *)
      | lexPragmaKey (ID(_, "terminates"), r) = (TERMINATES, r)
      | lexPragmaKey (ID(_, "block"), r) = (BLOCK, r) (* -cs 6/3/01 *)
      | lexPragmaKey (ID(_, "worlds"), r) = (WORLDS, r)
      | lexPragmaKey (ID(_, "covers"), r) = (COVERS, r)
      | lexPragmaKey (ID(_, "total"), r) = (TOTAL, r) (* -fp 3/18/01 *)
      | lexPragmaKey (ID(_, "reduces"), r) = (REDUCES, r)         (* -bp 6/5/99 *)
      | lexPragmaKey (ID(_, "tabled"), r) = (TABLED, r)           (* -bp 20/11/01 *)
      | lexPragmaKey (ID(_, "keepTable"), r) = (KEEPTABLE, r)     (* -bp 20/11/04 *)
      | lexPragmaKey (ID(_, "theorem"), r) = (THEOREM, r)
      | lexPragmaKey (ID(_, "prove"), r) = (PROVE, r)
      | lexPragmaKey (ID(_, "establish"), r) = (ESTABLISH, r)
      | lexPragmaKey (ID(_, "assert"), r) = (ASSERT, r)
      | lexPragmaKey (ID(_, "abbrev"), r) = (ABBREV, r)
      | lexPragmaKey (ID(_, "name"), r) = (NAME, r)
      | lexPragmaKey (ID(_, "define"), r) = (DEFINE, r) (* -rv 8/27/01 *)
      | lexPragmaKey (ID(_, "solve"), r) = (SOLVE, r)
      | lexPragmaKey (ID(_, "query"), r) = (QUERY, r)
      | lexPragmaKey (ID(_, "fquery"), r) = (FQUERY, r)
      | lexPragmaKey (ID(_, "compile"), r) = (COMPILE, r) (* -ABP 4/4/03 *)
      | lexPragmaKey (ID(_, "querytabled"), r) = (QUERYTABLED, r)
      | lexPragmaKey (ID(_, "trustme"), r) = (TRUSTME, r)
      | lexPragmaKey (ID(_, "subord"), r) = (SUBORD, r) (* -gaw 07/11/08 *)
      | lexPragmaKey (ID(_, "freeze"), r) = (FREEZE, r)
      | lexPragmaKey (ID(_, "thaw"), r) = (THAW, r)
      | lexPragmaKey (ID(_, "deterministic"), r) = (DETERMINISTIC, r) (* -rv 11/27/01 *)
      | lexPragmaKey (ID(_, "clause"), r) = (CLAUSE, r) (* -fp 08/09/02 *)
      | lexPragmaKey (ID(_, "sig"), r) = (SIG, r)
      | lexPragmaKey (ID(_, "struct"), r) = (STRUCT, r)
      | lexPragmaKey (ID(_, "where"), r) = (WHERE, r)
      | lexPragmaKey (ID(_, "include"), r) = (INCLUDE, r)
      | lexPragmaKey (ID(_, "open"), r) = (OPEN, r)
      | lexPragmaKey (ID(_, "use"), r) = (USE, r)
      | lexPragmaKey (ID(_, s), r) =
        error (r, "Unknown keyword %" ^ s ^ " (single line comment starts with `%<whitespace>' or `%%')")
      (* comments are now started by %<whitespace> *)
      (*
      | lexPragmaKey (_, (_,j)) = lexComment (char(j), j+1)
      *)

    and lexComment (#"\n", i) = lexInitial (char(i), i+1)
      | lexComment (#"%", i) = lexCommentPercent (char(i), i+1)
      | lexComment (#"\^D", i) =
          error (P.Reg (i-1, i-1), "Unclosed single-line comment at end of file")
          (* recover: (EOF, (i-1,i-1)) *)
      | lexComment (c, i) = lexComment (char(i), i+1)

    and lexCommentPercent (#".", i) = (EOF, P.Reg (i-2, i))
      | lexCommentPercent (c, i) = lexComment (c, i)

    and lexPercentBrace (c, i) = lexDComment (c, 1, i)

    (* functions lexing delimited comments below take nesting level l *)
    and lexDComment (#"}", l, i) = lexDCommentRBrace (char(i), l, i+1)
      | lexDComment (#"%", l, i) = lexDCommentPercent (char(i), l, i+1)
      | lexDComment (#"\^D", l, i) =
          (* pass comment beginning for error message? *)
          error (P.Reg (i-1,i-1), "Unclosed delimited comment at end of file")
          (* recover: (EOF, (i-1,i-1)) *)
      | lexDComment (c, l, i) = lexDComment (char(i), l, i+1)

    and lexDCommentPercent (#"{", l, i) = lexDComment (char(i), l+1, i+1)
      | lexDCommentPercent (#".", l, i) =
          error (P.Reg (i-2, i), "Unclosed delimited comment at end of file token `%.'")
          (* recover: (EOF, (i-2,i)) *)
      | lexDCommentPercent (c, l, i) = lexDComment (c, l, i)

    and lexDCommentRBrace (#"%", 1, i) = lexInitial (char(i), i+1)
      | lexDCommentRBrace (#"%", l, i) = lexDComment (char(i), l-1, i+1)
      | lexDCommentRBrace (c, l, i) = lexDComment (c, l, i)

    and lexString (P.Reg(i, j)) =
          (case char(j)
             of (#"\"") => (STRING (string (i, j+1)), P.Reg(i, j+1))
              | (#"\n") =>
                  error (P.Reg (i-1, i-1), "Unclosed string constant at end of line")
                  (* recover: (EOL, (i-1,i-1)) *)
              | (#"\^D") =>
                  error (P.Reg (i-1, i-1), "Unclosed string constant at end of file")
                  (* recover: (EOF, (i-1,i-1)) *)
              | _ => lexString (P.Reg(i, j+1)))

    fun lexContinue (j) = Stream.delay (fn () => lexContinue' (j))
    and lexContinue' (j) = lexContinue'' (lexInitial (char(j), j+1))

    and lexContinue'' (mt as (ID _, P.Reg (i,j))) =
          Stream.Cons (mt, lexContinueQualId (j))
      | lexContinue'' (mt as (token, P.Reg (i,j))) =
          Stream.Cons (mt, lexContinue (j))

    and lexContinueQualId (j) =
          Stream.delay (fn () => lexContinueQualId' (j))
    and lexContinueQualId' (j) =
          if char (j) = #"."
            then if isIdChar (char (j+1))
                   then Stream.Cons ((PATHSEP, P.Reg (j,j+1)), lexContinue (j+1))
                 else Stream.Cons ((DOT, P.Reg (j,j+1)), lexContinue (j+1))
          else lexContinue' (j)

  in
    lexContinue (0)
  end  (* fun lex (inputFun) = let ... in ... end *)

  fun lexStream (instream) = lex (fn i => Compat.inputLine97 (instream))

  fun lexTerminal (prompt0, prompt1) =
        lex (fn 0 => (print (prompt0) ;
                      Compat.inputLine97 (TextIO.stdIn))
              | i => (print (prompt1) ;
                      Compat.inputLine97 (TextIO.stdIn)))

  fun toString' (DOT) = "."
    | toString' (PATHSEP) = "."
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
    | toString' (DEFINE) = "%define"    (* -rv 8/27/01 *)
    | toString' (SOLVE) = "%solve"
    | toString' (QUERY) = "%query"
    | toString' (FQUERY) = "%fquery"
    | toString' (COMPILE) = "%compile"  (* -ABP 4/4/03 *)
    | toString' (QUERYTABLED) = "%querytabled"
    | toString' (MODE) = "%mode"
    | toString' (UNIQUE) = "%unique"
    | toString' (COVERS) = "%covers"
    | toString' (TOTAL) = "%total"
    | toString' (TERMINATES) = "%terminates"
    | toString' (BLOCK) = "%block"      (* -cs 6/3/01. *)
    | toString' (WORLDS) = "%worlds"
    | toString' (REDUCES) = "%reduces"              (*  -bp 6/5/99. *)
    | toString' (TABLED) = "%tabled"                (*  -bp 20/11/01. *)
    | toString' (KEEPTABLE) = "%keepTable"          (*  -bp 04/11/03. *)
    | toString' (THEOREM) = "%theorem"
    | toString' (PROVE) = "%prove"
    | toString' (ESTABLISH) = "%establish"
    | toString' (ASSERT) = "%assert"
    | toString' (ABBREV) = "%abbrev"
    | toString' (TRUSTME) = "%trustme"
    | toString' (SUBORD) = "%subord"
    | toString' (FREEZE) = "%freeze"
    | toString' (THAW) = "%thaw"
    | toString' (DETERMINISTIC) = "%deterministic"  (* -rv 11/27/01. *)
    | toString' (CLAUSE) = "%clause" (* -fp 08/09/02 *)
    | toString' (SIG) = "%sig"
    | toString' (STRUCT) = "%struct"
    | toString' (WHERE) = "%where"
    | toString' (INCLUDE) = "%include"
    | toString' (OPEN) = "%open"
    | toString' (USE) = "%use"

 fun toString (ID(_,s)) = "identifier `" ^ s ^ "'"
   | toString (EOF) = "end of file or `%.'"
   | toString (STRING(s)) = "constant string " ^ s
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

  end  (* local ... *)

end;  (* functor Lexer *)

structure Lexer =
  Lexer (structure Stream' = Stream
         (*! structure Paths' = Paths !*)
           );
