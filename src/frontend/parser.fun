(* Top-Level Parser *)
(* Author: Frank Pfenning *)

functor Parser (structure Parsing' : PARSING
		structure Stream' : STREAM (* result stream *)
		structure ExtSyn' : EXTSYN
		structure ExtSynQ' : EXTSYN
		structure Names' : NAMES
		structure ExtModes' : EXTMODES
		structure ThmExtSyn' : THMEXTSYN
		structure ParseConDec : PARSE_CONDEC
		  sharing ParseConDec.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseConDec.ExtSyn = ExtSyn'
		structure ParseQuery : PARSE_QUERY
		  sharing ParseQuery.Parsing.Lexer = Parsing'.Lexer
		  sharing type ParseQuery.ExtSyn.term = ExtSynQ'.term
		  sharing type ParseQuery.ExtSyn.query = ExtSynQ'.query
		structure ParseFixity : PARSE_FIXITY
		  sharing ParseFixity.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseFixity.Names = Names' 
                structure ParseMode : PARSE_MODE
		  sharing ParseMode.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseMode.ExtModes = ExtModes'
	        structure ParseThm : PARSE_THM
		  sharing ParseThm.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseThm.ThmExtSyn = ThmExtSyn'
                structure ParseTermQ : PARSE_TERM 
                  sharing ParseTermQ.Parsing.Lexer = Parsing'.Lexer
                  sharing type ParseTermQ.ExtSyn.term = ExtSynQ'.term
		  sharing type ParseTermQ.ExtSyn.query = ExtSynQ'.query)
  : PARSER =
struct

  structure Parsing = Parsing'
  structure Stream = Stream'
  structure ExtSyn = ExtSyn'
  structure ExtSynQ = ExtSynQ'
  structure Names = Names'
  structure ExtModes = ExtModes'
  structure ThmExtSyn = ThmExtSyn'

  datatype fileParseResult =
      ConDec of ExtSyn.condec * ExtSyn.Paths.region
    | FixDec of (string * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (string * ExtSyn.Paths.region) * (string * string option)
    | ModeDec of ExtModes.modedec
    | TerminatesDec of ThmExtSyn.tdecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSynQ.query * ExtSyn.Paths.region (* expected, try, A *)
    | Solve of (string * ExtSynQ.term) * ExtSyn.Paths.region
    (* Further pragmas to be added later here *)

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    fun stripDot (LS.Cons((L.DOT, r), s)) = s
      | stripDot (LS.Cons((L.RPAREN, r), s)) =
	  Parsing.error (r, "Unexpected right parenthesis")
      | stripDot (LS.Cons((L.RBRACE, r), s)) =
	  Parsing.error (r, "Unexpected right brace")
      | stripDot (LS.Cons((L.RBRACKET, r), s)) =
	  Parsing.error (r, "Unexpected right bracket")
      | stripDot (LS.Cons ((L.EOF, r), s)) =
	  Parsing.error (r, "Unexpected end of file")
      | stripDot (LS.Cons ((L.EQUAL, r), s)) =
	  Parsing.error (r, "Unexpected `='")
      | stripDot (LS.Cons ((t, r), s)) =
	  Parsing.error (r, "Expected `.', found " ^ L.toString t)
      (* Everything else should be impossible *)

    (*
    fun stripOptionalDot (LS.Cons ((L.DOT,r), s)) = s
      | stripOptionalDot f = LS.delay (fn () => f)
    *)

    fun parseBound' (LS.Cons ((L.ID (_, "*"), r), s')) = (NONE, s')
      | parseBound' (LS.Cons ((L.ID (_, name), r), s')) =
        ((SOME (L.stringToNat (name)), s')
	 handle Overflow => Parsing.error (r, "Bound too large")
	      | L.NotDigit _ => Parsing.error (r, "Bound `" ^ name ^ "' neither `*' nor a natural number"))
      | parseBound' (LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected bound `*' or natural number, found "
			    ^ L.toString t)

    fun parseID' (LS.Cons ((L.ID (_, name), r), s')) = (name, s')
      | parseID' (LS.Cons ((t,r), s')) =
          Parsing.error (r, "Expected identifier, found " ^ L.toString t)

    fun parseColon (LS.Cons ((L.COLON, r), s')) = s'
      | parseColon (LS.Cons ((t,r), s')) =
          Parsing.error (r, "Expected `:', found " ^ L.toString t)

    fun parseStream (s) =
          Stream.delay (fn () => parseStream' (LS.expose s))

    (* parseStream' : lexResult front -> fileParseResult front *)
    (* parseStream' switches between various specialized parsers *)
    and parseStream' (f as LS.Cons ((L.ID (idCase,name), r0), s')) = parseConDec' (f)
      | parseStream' (f as LS.Cons ((L.UNDERSCORE, r), s')) = parseConDec' (f)
      | parseStream' (f as LS.Cons ((L.INFIX, r), s')) = parseFixity' f
      | parseStream' (f as LS.Cons ((L.PREFIX, r), s')) = parseFixity' f
      | parseStream' (f as LS.Cons ((L.POSTFIX, r), s')) = parseFixity' f
      | parseStream' (f as LS.Cons ((L.NAME, r), s')) =
	let
	  val (namePref, f') = ParseFixity.parseNamePref' f
	in
	  Stream.Cons (NamePref namePref, parseStream (stripDot f'))
	end
      | parseStream' (f as LS.Cons((L.SOLVE, r0), s')) =
	let
	  val (name, s1) = parseID' (LS.expose s')
	  val s2 = parseColon (LS.expose s1)
	  val (solve, f3 as LS.Cons((_,r'),_)) = ParseTermQ.parseTerm' (LS.expose s2)
	  val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons (Solve ((name, solve), r), parseStream (stripDot f3))
	end
      | parseStream' (LS.Cons((L.QUERY, r0), s')) =
        let
	  val (expected, s1) = parseBound' (LS.expose s')
	  val (try, s2) = parseBound' (LS.expose s1)
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s2)
	  val r = ExtSyn.Paths.join (r0, r')
        in 
          Stream.Cons (Query (expected, try, query, r), parseStream (stripDot f3))
        end
      | parseStream' (f as LS.Cons ((L.MODE, r), s')) = parseMode' f
      | parseStream' (f as LS.Cons ((L.TERMINATES, r), s')) = parseTerminates' f
      | parseStream' (f as LS.Cons ((L.THEOREM, r), s')) = parseTheorem' f
      | parseStream' (f as LS.Cons ((L.PROVE, r), s')) = parseProve' f
      | parseStream' (f as LS.Cons ((L.ESTABLISH, r), s')) = parseEstablish' f
      | parseStream' (f as LS.Cons ((L.ASSERT, r), s')) = parseAssert' f
      | parseStream' (LS.Cons ((L.EOF, r), s')) = Stream.Empty
      | parseStream' (LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected constant name or pragma keyword, found "
			    ^ L.toString t)

    and parseConDec' (f as LS.Cons ((_, r0), _)) =
        let
	  val (conDec, f' as LS.Cons((_,r'),_)) = ParseConDec.parseConDec' (f)
	  val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons (ConDec (conDec, r), parseStream (stripDot f'))
	end

    and parseFixity' (f) =
        let
	  val (fdec, f') = ParseFixity.parseFixity' (f)
	in
	  Stream.Cons (FixDec fdec, parseStream (stripDot f'))
	end

    and parseMode' (f) =
        let
	  val (mdec, f') = ParseMode.parseMode' (f)
	in
	  Stream.Cons (ModeDec mdec, parseStream (stripDot f'))
	end

    and parseTerminates' (f) =
        let
	  val (ldec, f') = ParseThm.parseTerminates' (f)
	in
	  Stream.Cons (TerminatesDec ldec, parseStream (stripDot f'))
	end

    and parseTheorem' (f) =
        let
	  val (ldec, f') = ParseThm.parseTheoremDec' (f)
	in
	  Stream.Cons (TheoremDec ldec, parseStream (stripDot f'))
	end

    and parseProve' (f) =
        let
	  val (ldec, f') = ParseThm.parseProve' (f)
	in
	  Stream.Cons (ProveDec ldec, parseStream (stripDot f'))
	end

    and parseEstablish' (f) =
        let
	  val (ldec, f') = ParseThm.parseEstablish' (f)
	in
	  Stream.Cons (EstablishDec ldec, parseStream (stripDot f'))
	end

    and parseAssert' (f) =
        let
	  val (ldec, f') = ParseThm.parseAssert' (f)
	in
	  Stream.Cons (AssertDec ldec, parseStream (stripDot f'))
	end

    fun parseQ (s) = Stream.delay (fn () => parseQ' (LS.expose s))
    and parseQ' (f) =
        let
	  val (query, f') = ParseQuery.parseQuery' (f)
	in
	  Stream.Cons (query, parseQ (stripDot (f')))
	end

  in

    val parseStream = (fn instream => parseStream (L.lexStream (instream)))

    fun parseTerminalQ prompts = parseQ (L.lexTerminal prompts)
        
  end  (* local ... in *)

end;  (* functor Parser *)
