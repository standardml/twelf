(* Top-Level Parser *)
(* Author: Frank Pfenning *)

functor Parser ((*! structure Parsing' : PARSING !*)
                structure Stream' : STREAM (* result stream *)
                structure ExtSyn' : EXTSYN
                (*! sharing ExtSyn'.Paths = Parsing'.Lexer.Paths !*)
                structure Names' : NAMES
                structure ExtConDec' : EXTCONDEC
                structure ExtQuery' : EXTQUERY
                structure ExtModes' : EXTMODES
                structure ThmExtSyn' : THMEXTSYN
                structure ModExtSyn' : MODEXTSYN
                structure ParseConDec : PARSE_CONDEC
                (*! sharing ParseConDec.Lexer = Parsing'.Lexer !*)
                  sharing ParseConDec.ExtConDec = ExtConDec'
                structure ParseQuery : PARSE_QUERY
                (*! sharing ParseQuery.Lexer = Parsing'.Lexer !*)
                  sharing ParseQuery.ExtQuery = ExtQuery'
                structure ParseFixity : PARSE_FIXITY
                (*! sharing ParseFixity.Lexer = Parsing'.Lexer !*)
                  sharing ParseFixity.Names = Names'
                structure ParseMode : PARSE_MODE
                (*! sharing ParseMode.Lexer = Parsing'.Lexer !*)
                  sharing ParseMode.ExtModes = ExtModes'
                structure ParseThm : PARSE_THM
                (*! sharing ParseThm.Lexer = Parsing'.Lexer !*)
                  sharing ParseThm.ThmExtSyn = ThmExtSyn'
                structure ParseModule : PARSE_MODULE
                (*! sharing ParseModule.Parsing = Parsing' !*)
                  sharing ParseModule.ModExtSyn = ModExtSyn'
                structure ParseTerm : PARSE_TERM
                (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
                  sharing ParseTerm.ExtSyn = ExtSyn')
  : PARSER =
struct

  (*! structure Parsing = Parsing' !*)
  structure Stream = Stream'
  structure ExtSyn = ExtSyn'
  structure Names = Names'
  structure ExtConDec = ExtConDec'
  structure ExtQuery = ExtQuery'
  structure ExtModes = ExtModes'
  structure ThmExtSyn = ThmExtSyn'
  structure ModExtSyn = ModExtSyn'

  datatype fileParseResult =
      ConDec of ExtConDec.condec
    | FixDec of (Names.Qid * Paths.region) * Names.Fixity.fixity
    | NamePref of (Names.Qid * Paths.region) * (string list * string list)
    | ModeDec of ExtModes.modedec list
    | UniqueDec of ExtModes.modedec list (* -fp 8/17/03 *)
    | CoversDec of ExtModes.modedec list
    | TotalDec of ThmExtSyn.tdecl
    | TerminatesDec of ThmExtSyn.tdecl
    | WorldDec of ThmExtSyn.wdecl
    | ReducesDec of ThmExtSyn.rdecl   (* -bp *)
    | TabledDec of ThmExtSyn.tableddecl
    | KeepTableDec of ThmExtSyn.keepTabledecl
    | TheoremDec of ThmExtSyn.theoremdec
    | ProveDec of ThmExtSyn.prove
    | EstablishDec of ThmExtSyn.establish
    | AssertDec of ThmExtSyn.assert
    | Query of int option * int option * ExtQuery.query (* expected, try, A *)
    | FQuery of ExtQuery.query (* expected, try, A *)
    | Compile of Names.Qid list (* -ABP 4/4/03 *)
    | Querytabled of int option * int option * ExtQuery.query        (* numSol, try, A *)
    | Solve of ExtQuery.define list * ExtQuery.solve
    | AbbrevDec of ExtConDec.condec
    | TrustMe of fileParseResult * Paths.region (* -fp *)
    | SubordDec of (Names.Qid * Names.Qid) list (* -gaw *)
    | FreezeDec of Names.Qid list
    | ThawDec of Names.Qid list
    | DeterministicDec of Names.Qid list  (* -rv *)
    | ClauseDec of ExtConDec.condec (* -fp *)
    | SigDef of ModExtSyn.sigdef
    | StructDec of ModExtSyn.structdec
    | Include of ModExtSyn.sigexp
    | Open of ModExtSyn.strexp
    | BeginSubsig | EndSubsig (* enter/leave a new context *)
    | Use of string
    (* Further pragmas to be added later here *)

  local
    structure L = Lexer
    structure LS = Lexer.Stream

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
          val r = Paths.join (r1, r2)
        in
          Stream.Cons ((NamePref namePref, r), parseStream (stripDot f', sc))
        end
      | parseStream' (f as LS.Cons((L.DEFINE, r), s'), sc) =
          parseSolve' (f, sc)
      | parseStream' (f as LS.Cons((L.SOLVE, r), s'), sc) =
          parseSolve' (f, sc)
      | parseStream' (LS.Cons((L.QUERY, r0), s'), sc) =
        let
          val (expected, s1) = parseBound' (LS.expose s')
          val (try, s2) = parseBound' (LS.expose s1)
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s2)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((Query (expected, try, query), r), parseStream (stripDot f3, sc))
        end
      | parseStream' (LS.Cons((L.FQUERY, r0), s'), sc) =
        let
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s')
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((FQuery query, r), parseStream (stripDot f3, sc))
        end

      | parseStream' (LS.Cons((L.QUERYTABLED, r0), s'), sc) =
        let
          val (numSol, s1) = parseBound' (LS.expose s')
          val (try, s2) = parseBound' (LS.expose s1)
          val (query, f3 as LS.Cons((_,r'),_)) = ParseQuery.parseQuery' (LS.expose s2)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((Querytabled (numSol, try, query), r), parseStream (stripDot f3, sc))
        end
      | parseStream' (f as LS.Cons ((L.MODE, r), s'), sc) = parseMode' (f, sc)
      | parseStream' (f as LS.Cons ((L.UNIQUE, r), s'), sc) = parseUnique' (f, sc)
      | parseStream' (f as LS.Cons ((L.COVERS, r), s'), sc) = parseCovers' (f, sc)
      | parseStream' (f as LS.Cons ((L.TOTAL, r), s'), sc) = parseTotal' (f, sc) (* -fp *)
      | parseStream' (f as LS.Cons ((L.TERMINATES, r), s'), sc) = parseTerminates' (f, sc)
      | parseStream' (f as LS.Cons ((L.BLOCK, r), s'), sc) = parseConDec' (f, sc) (* -cs *)
      | parseStream' (f as LS.Cons ((L.WORLDS, r), s'), sc) = parseWorlds' (f, sc)
      | parseStream' (f as LS.Cons ((L.REDUCES, r), s'), sc) = parseReduces' (f, sc) (* -bp *)
      | parseStream' (f as LS.Cons ((L.TABLED, r), s'), sc) = parseTabled' (f, sc) (* -bp *)
      | parseStream' (f as LS.Cons ((L.KEEPTABLE, r), s'), sc) = parseKeepTable' (f, sc) (* -bp *)
      | parseStream' (f as LS.Cons ((L.THEOREM, r), s'), sc) = parseTheorem' (f, sc)
      | parseStream' (f as LS.Cons ((L.PROVE, r), s'), sc) = parseProve' (f, sc)
      | parseStream' (f as LS.Cons ((L.ESTABLISH, r), s'), sc) = parseEstablish' (f, sc)
      | parseStream' (f as LS.Cons ((L.ASSERT, r), s'), sc) = parseAssert' (f, sc)
      | parseStream' (f as LS.Cons ((L.TRUSTME, r), s'), sc) = parseTrustMe' (f, sc)
      | parseStream' (f as LS.Cons ((L.FREEZE, r), s'), sc) = parseFreeze' (f, sc)
      | parseStream' (f as LS.Cons ((L.SUBORD, r), s'), sc) = parseSubord' (f, sc)
      | parseStream' (f as LS.Cons ((L.THAW, r), s'), sc) = parseThaw' (f, sc)
      | parseStream' (f as LS.Cons ((L.DETERMINISTIC, r), s'), sc) = parseDeterministic' (f, sc) (* -rv *)
      | parseStream' (f as LS.Cons ((L.COMPILE, r), s'), sc) = parseCompile' (f, sc) (* -ABP 4/4/03 *)
      | parseStream' (f as LS.Cons ((L.CLAUSE, r), s'), sc) = parseClause' (f, sc) (* -fp *)
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
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((ConDec conDec, r), parseStream (stripDot f', sc))
        end

    and parseAbbrev' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (conDec, f' as LS.Cons ((_,r'),_)) = ParseConDec.parseAbbrev' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((AbbrevDec conDec, r), parseStream (stripDot f', sc))
        end

    and parseClause' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (conDec, f' as LS.Cons ((_,r'),_)) = ParseConDec.parseClause' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((ClauseDec conDec, r), parseStream (stripDot f', sc))
        end

    and parseFixity' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (fdec, f' as LS.Cons ((_,r'),_)) = ParseFixity.parseFixity' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((FixDec fdec, r), parseStream (stripDot f', sc))
        end

    and parseSolve' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (defnssolve, f' as LS.Cons ((_,r'),_)) = ParseQuery.parseSolve' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((Solve defnssolve, r), parseStream (stripDot f', sc))
        end

    and parseMode' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (mdecs, f' as LS.Cons ((_,r'),_)) = ParseMode.parseMode' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((ModeDec mdecs, r), parseStream (stripDot f', sc))
        end

    and parseUnique' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (mdecs, f' as LS.Cons ((_,r'),_)) = ParseMode.parseMode' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((UniqueDec mdecs, r), parseStream (stripDot f', sc))
        end

    and parseCovers' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (mdecs, f' as LS.Cons ((_, r'), _)) = ParseMode.parseMode' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((CoversDec mdecs, r), parseStream (stripDot f', sc))
        end

    and parseTotal' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTotal' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((TotalDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseTerminates' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTerminates' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((TerminatesDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseReduces' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseReduces' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((ReducesDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseTabled' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTabled' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((TabledDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseKeepTable' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseKeepTable' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((KeepTableDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseWorlds' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseWorlds' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((WorldDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseTheorem' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseTheoremDec' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((TheoremDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseProve' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseProve' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((ProveDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseEstablish' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseEstablish' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((EstablishDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseAssert' (f as LS.Cons ((_, r0), _), sc) =
        let
          val (ldec, f' as LS.Cons ((_, r'), _)) = ParseThm.parseAssert' (f)
          val r = Paths.join (r0, r')
        in
          Stream.Cons ((AssertDec ldec, r), parseStream (stripDot f', sc))
        end

    and parseTrustMe' (f as LS.Cons ((_, r0), s), sc) =
        let
          fun parseNextDec' (Stream.Cons((dec,r),s')) =
                 Stream.Cons ((TrustMe(dec,r),r0),s')
            | parseNextDec' (Stream.Empty) =
                 Parsing.error (r0, "No declaration after `%trustme'")
        in
          parseNextDec' (parseStream' (LS.expose s, sc))
        end

    and parseSubord' (f as LS.Cons ((_, r0), s), sc) =
        let
          val (qidpairs, f' as LS.Cons ((_, r'), _)) = ParseTerm.parseSubord' (LS.expose s)
          val r = Paths.join (r0, r')
          val qidpairs = map (fn (qid1, qid2) => (Names.Qid qid1, Names.Qid qid2)) qidpairs
        in
          Stream.Cons ((SubordDec qidpairs, r), parseStream (stripDot f', sc))
        end

    and parseFreeze' (f as LS.Cons ((_, r0), s), sc) =
        let
          val (qids, f' as LS.Cons ((_, r'), _)) = ParseTerm.parseFreeze' (LS.expose s)
          val r = Paths.join (r0, r')
          val qids = map Names.Qid qids
        in
          Stream.Cons ((FreezeDec qids, r), parseStream (stripDot f', sc))
        end

    and parseThaw' (f as LS.Cons ((_, r0), s), sc) =
        let
          val (qids, f' as LS.Cons ((_, r'), _)) = ParseTerm.parseThaw' (LS.expose s)
          val r = Paths.join (r0, r')
          val qids = map Names.Qid qids
        in
          Stream.Cons ((ThawDec qids, r), parseStream (stripDot f', sc))
        end

    and parseDeterministic' (f as LS.Cons ((_, r0), s), sc) =
        let
          val (qids, f' as LS.Cons ((_, r'), _)) = ParseTerm.parseDeterministic' (LS.expose s)
          val r = Paths.join (r0, r')
          val qids = map Names.Qid qids
        in
          Stream.Cons ((DeterministicDec qids, r), parseStream (stripDot f', sc))
        end

    (* ABP 4/4/03 *)
    and parseCompile' (f as LS.Cons ((_, r0), s), sc) =
        let
          val (qids, f' as LS.Cons ((_, r'), _)) = ParseTerm.parseCompile' (LS.expose s)
          val r = Paths.join (r0, r')
          val qids = map Names.Qid qids
        in
          Stream.Cons ((Compile qids, r), parseStream (stripDot f', sc))
        end


    and parseSigDef' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (sigdef, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((SigDef sigdef, Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModule.parseSigDef', parseStream, finish)
        end

    and parseStructDec' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (structdec, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((StructDec structdec, Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModule.parseStructDec', parseStream, finish)
        end

    and parseInclude' (f as LS.Cons ((_, r1), _), sc) =
        let
          fun finish (sigexp, f' as LS.Cons ((_, r2), _)) =
                Stream.Cons ((Include sigexp, Paths.join (r1, r2)),
                             parseStream (stripDot f', sc))
        in
          recParse' (f, ParseModule.parseInclude', parseStream, finish)
        end

    and parseOpen' (f as LS.Cons ((_, r1), _), sc) =
        let
          val (strexp, f' as LS.Cons ((_, r2), _)) =
                ParseModule.parseOpen' (f)
        in
          Stream.Cons ((Open strexp, Paths.join (r1, r2)),
                       parseStream (stripDot f', sc))
        end

    and parseUse' (LS.Cons ((L.ID (_,name), r0), s), sc) =
        let
          val f as LS.Cons ((_, r'), _) = LS.expose s
          val r = Paths.join (r0, r')
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
