(* Top-Level Parser *)
(* Author: Frank Pfenning *)

functor Parser (structure Parsing' : PARSING
		structure Stream' : STREAM (* result stream *)
		structure ExtSyn' : EXTSYN
		  sharing ExtSyn'.Paths = Parsing'.Lexer.Paths
		structure Names' : NAMES
		structure ExtModes' : EXTMODES
		structure ThmExtSyn' : THMEXTSYN
                structure ModExtSyn' : MODEXTSYN
		structure ParseConDec : PARSE_CONDEC
		  sharing ParseConDec.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseConDec.ExtSyn = ExtSyn'
		structure ParseQuery : PARSE_QUERY
		  sharing ParseQuery.Parsing.Lexer = Parsing'.Lexer
                  sharing ParseQuery.ExtSyn = ExtSyn'
		structure ParseFixity : PARSE_FIXITY
		  sharing ParseFixity.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseFixity.Names = Names' 
                structure ParseMode : PARSE_MODE
		  sharing ParseMode.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseMode.ExtModes = ExtModes'
	        structure ParseThm : PARSE_THM
		  sharing ParseThm.Parsing.Lexer = Parsing'.Lexer
		  sharing ParseThm.ThmExtSyn = ThmExtSyn'
                structure ParseModules : PARSE_MODULES
                  sharing ParseModules.Parsing = Parsing'
                  sharing ParseModules.ModExtSyn = ModExtSyn'
                structure ParseTerm : PARSE_TERM 
                  sharing ParseTerm.Parsing.Lexer = Parsing'.Lexer
                  sharing ParseTerm.ExtSyn = ExtSyn')
  : PARSER =
struct

  structure Parsing = Parsing'
  structure Stream = Stream'
  structure ExtSyn = ExtSyn'
  structure Names = Names'
  structure ExtModes = ExtModes'
  structure ThmExtSyn = ThmExtSyn'
  structure ModExtSyn = ModExtSyn'

  datatype fileParseResult =
      ConDec of ExtSyn.condec
    | FixDec of (Names.Qid * ExtSyn.Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.Qid * ExtSyn.Paths.region) * (string * string option)
    | ModeDec of ExtModes.modedec list
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl	(* -fp *)
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl  (* -bp *)
    | TheoremDec of ThmExtSyn.theoremdec 
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtSyn.query (* expected, try, A *)
    | Querytabled of int option * ExtSyn.query        (* expected, try, A *)
    | Solve of (string * ExtSyn.term)
    | AbbrevDec of ExtSyn.condec
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig | EndSubsig (* enter/leave a new context *)
    | Use of string
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

    fun parseEqual (LS.Cons ((L.EQUAL, r), s')) = s'
      | parseEqual (LS.Cons ((t,r), s')) =
          Parsing.error (r, "Expected `=', found " ^ L.toString t)

    (* pass parseStream as theSigParser in order to be able to use
       this function polymorphically in the definition of parseStream *)
    fun recParse (s, recparser, theSigParser, sc) =
          Stream.delay (fn () => recParse' (LS.expose s, recparser, theSigParser, sc))
    and recParse' (f, recparser, theSigParser, sc) =
        (case recparser f
           of (Parsing.Done x, f') => sc (x, f')
            | (Parsing.Continuation k, LS.Cons ((L.LBRACE, r1), s')) =>
              let
                fun finish (LS.Cons ((L.RBRACE, r2), s'')) =
                      Stream.Cons ((EndSubsig, r2), recParse (s'', k, theSigParser, sc))
                  | finish (LS.Cons ((t, r), _)) =
                      Parsing.error (r, "Expected `}', found " ^ L.toString t)
              in
                Stream.Cons ((BeginSubsig, r1), theSigParser (s', finish))
              end
            | (Parsing.Continuation _, LS.Cons ((t, r), _)) => 
                Parsing.error (r, "Expected `{', found " ^ L.toString t))

    fun parseStream (s, sc) =
          Stream.delay (fn () => parseStream' (LS.expose s, sc))

    (* parseStream' : lexResult front -> fileParseResult front *)
    (* parseStream' switches between various specialized parsers *)
    and parseStream' (f as LS.Cons ((L.ID (idCase,name), r0), s'), sc) = parseConDec' (f, sc)
      | parseStream' (f as LS.Cons ((L.ABBREV, r), s'), sc) = parseAbbrev' (f, sc)
      | parseStream' (f as LS.Cons ((L.UNDERSCORE, r), s'), sc) = parseConDec' (f, sc)
      | parseStream' (f as LS.Cons ((L.INFIX, r), s'), sc) = parseFixity' (f, sc)
      | parseStream' (f as LS.Cons ((L.PREFIX, r), s'), sc) = parseFixity' (f, sc)
      | parseStream' (f as LS.Cons ((L.POSTFIX, r), s'), sc) = parseFixity' (f, sc)
      | parseStream' (f as LS.Cons ((L.NAME, r1), s'), sc) =
	let
	  val (namePref, f' as LS.Cons ((_, r2), _)) = ParseFixity.parseNamePref' f
          val r = ExtSyn.Paths.join (r1, r2)
	in
	  Stream.Cons ((NamePref namePref, r), parseStream (stripDot f', sc))
	end
      | parseStream' (f as LS.Cons((L.SOLVE, r0), s'), sc) =
	let
	  val (name, s1) = parseID' (LS.expose s')
	  val s2 = parseColon (LS.expose s1)
	  val (solve, f3 as LS.Cons((_,r'),_)) = ParseTerm.parseTerm' (LS.expose s2)
	  val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((Solve (name, solve), r), parseStream (stripDot f3, sc))
	end
      | parseStream' (LS.Cons((L.QUERY, r0), s'), sc) =
        let
	  val (expected, s1) = parseBound' (LS.expose s')
	  val (try, s2) = parseBound' (LS.expose s1)
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s2)
	  val r = ExtSyn.Paths.join (r0, r')
        in 
          Stream.Cons ((Query (expected, try, query), r), parseStream (stripDot f3, sc))
        end
      | parseStream' (LS.Cons((L.QUERYTABLED, r0), s'), sc) =
        let
	  val (try, s2) = parseBound' (LS.expose s')
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s2)
	  val r = ExtSyn.Paths.join (r0, r')
        in 
          Stream.Cons ((Querytabled (try, query), r), parseStream (stripDot f3, sc))
        end 
      | parseStream' (f as LS.Cons ((L.MODE, r), s'), sc) = parseMode' (f, sc)
      | parseStream' (f as LS.Cons ((L.COVERS, r), s'), sc) = parseCovers' (f, sc)
      | parseStream' (f as LS.Cons ((L.TOTAL, r), s'), sc) = parseTotal' (f, sc) (* -fp *)
      | parseStream' (f as LS.Cons ((L.TERMINATES, r), s'), sc) = parseTerminates' (f, sc)
      | parseStream' (f as LS.Cons ((L.BLOCK, r), s'), sc) = parseConDec' (f, sc) (* -cs *)
      | parseStream' (f as LS.Cons ((L.WORLDS, r), s'), sc) = parseWorlds' (f, sc)
      | parseStream' (f as LS.Cons ((L.REDUCES, r), s'), sc) = parseReduces' (f, sc) (* -bp *)
      | parseStream' (f as LS.Cons ((L.THEOREM, r), s'), sc) = parseTheorem' (f, sc)
      | parseStream' (f as LS.Cons ((L.PROVE, r), s'), sc) = parseProve' (f, sc)
      | parseStream' (f as LS.Cons ((L.ESTABLISH, r), s'), sc) = parseEstablish' (f, sc)
      | parseStream' (f as LS.Cons ((L.ASSERT, r), s'), sc) = parseAssert' (f, sc)
      | parseStream' (f as LS.Cons ((L.SIG, r), s'), sc) = parseSigDef' (f, sc)
      | parseStream' (f as LS.Cons ((L.STRUCT, r), s'), sc) = parseStructDec' (f, sc)
      | parseStream' (f as LS.Cons ((L.INCLUDE, r), s'), sc) = parseInclude' (f, sc)
      | parseStream' (f as LS.Cons ((L.OPEN, r), s'), sc) = parseOpen' (f, sc)
      | parseStream' (f as LS.Cons ((L.USE, r), s'), sc) = parseUse' (LS.expose s', sc)
      | parseStream' (f as LS.Cons ((L.EOF, _), _), sc) = sc f
      | parseStream' (f as LS.Cons ((L.RBRACE, _), _), sc) = sc f
      | parseStream' (LS.Cons ((t,r), s'), sc) =
	  Parsing.error (r, "Expected constant name or pragma keyword, found "
			    ^ L.toString t)

    and parseConDec' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (conDec, f' as LS.Cons((_,r'),_)) = ParseConDec.parseConDec' (f)
	  val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((ConDec conDec, r), parseStream (stripDot f', sc))
	end

    and parseAbbrev' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (conDec, f' as LS.Cons ((_,r'),_)) = ParseConDec.parseAbbrev' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((AbbrevDec conDec, r), parseStream (stripDot f', sc))
	end

    and parseFixity' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (fdec, f' as LS.Cons ((_,r'),_)) = ParseFixity.parseFixity' (f)
          val r = ExtSyn.Paths.join (r0, r')            
	in
	  Stream.Cons ((FixDec fdec, r), parseStream (stripDot f', sc))
	end

    and parseMode' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (mdecs, f' as LS.Cons ((_,r'),_)) = ParseMode.parseMode' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((ModeDec mdecs, r), parseStream (stripDot f', sc))
	end

    and parseCovers' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (mdecs, f' as LS.Cons ((_, r'), _)) = ParseMode.parseMode' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((CoversDec mdecs, r), parseStream (stripDot f', sc))
	end

    and parseTotal' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTotal' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((TotalDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseTerminates' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTerminates' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((TerminatesDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseReduces' (f as LS.Cons ((_, r0), _), sc) = 
	let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseReduces' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((ReducesDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseWorlds' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseWorlds' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((WorldDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseTheorem' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTheoremDec' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((TheoremDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseProve' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseProve' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((ProveDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseEstablish' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseEstablish' (f)
          val r = ExtSyn.Paths.join (r0, r')
	in
	  Stream.Cons ((EstablishDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseAssert' (f as LS.Cons ((_, r0), _), sc) =
        let
	  val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseAssert' (f)
          val r = ExtSyn.Paths.join (r0, r')            
	in
	  Stream.Cons ((AssertDec ldec, r), parseStream (stripDot f', sc))
	end

    and parseSigDef' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (sigdef, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((SigDef sigdef, ExtSyn.Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModules.parseSigDef', parseStream, finish)
        end

    and parseStructDec' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (structdec, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((StructDec structdec, ExtSyn.Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModules.parseStructDec', parseStream, finish)
        end

    and parseInclude' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (sigexp, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((Include sigexp, ExtSyn.Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModules.parseInclude', parseStream, finish)
        end

    and parseOpen' (f as LS.Cons ((_, r1), _), sc) =
        let
          val (strexp, f' as LS.Cons ((_, r2), _)) =
                ParseModules.parseOpen' (f)
        in
          Stream.Cons ((Open strexp, ExtSyn.Paths.join (r1, r2)),
                       parseStream (stripDot f', sc))
        end

    and parseUse' (LS.Cons ((L.ID (_,name), r0), s), sc) =
        let
          val f as LS.Cons ((_, r'), _) = LS.expose s
          val r = ExtSyn.Paths.join (r0, r')
        in
          Stream.Cons ((Use name, r), parseStream (stripDot f, sc))
        end
      | parseUse' (LS.Cons ((_, r), _), sc) =
        Parsing.error (r, "Constraint solver name expected")

    fun parseQ (s) = Stream.delay (fn () => parseQ' (LS.expose s))
    and parseQ' (f) =
        let
	  val (query, f') = ParseQuery.parseQuery' (f)
	in
	  Stream.Cons (query, parseQ (stripDot (f')))
	end

    fun parseTLStream instream =
        let
          fun finish (LS.Cons ((L.EOF, r), s)) = Stream.Empty
            | finish (LS.Cons ((L.RBRACE, r), s)) =
                Parsing.error (r, "Unmatched `}'")
        in
          parseStream (L.lexStream instream, finish)
        end

  in

    val parseStream = parseTLStream

    fun parseTerminalQ prompts = parseQ (L.lexTerminal prompts)
        
  end  (* local ... in *)

end;  (* functor Parser *)
