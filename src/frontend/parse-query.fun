(* Parsing Queries *)
(* Author: Frank Pfenning *)

functor ParseQuery

  ((*! structure Parsing' : PARSING !*)
   structure ExtQuery' : EXTQUERY
   (*! sharing ExtQuery'.Paths = Parsing'.Lexer.Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ExtQuery'.ExtSyn)
  : PARSE_QUERY =
struct

  (*! structure Parsing = Parsing' !*)
  structure ExtQuery = ExtQuery'

  local
    structure L = Lexer
    structure LS = Lexer.Stream
    structure P = Paths

    fun returnQuery (optName, (tm, f)) = (ExtQuery.query (optName, tm), f)

    (* parseQuery1 (name, f, f')   ": A" from f' or "V" from f. *)

    fun parseQuery1 (name, f, LS.Cons ((L.COLON, r), s')) =
          returnQuery (SOME(name), ParseTerm.parseTerm' (LS.expose s'))
      | parseQuery1 (name, f, _) = returnQuery (NONE, ParseTerm.parseTerm' f)

    (* parseQuery' : lexResult front -> ExtQuery.query * lexResult front *)
    (* parseQuery'  "X : A" | "A" *)

    (* Query parsing is ambiguous, since a term "V" might have the form "U' : V'" *)
    (* We look for an uppercase variable X followed by a `:'.
       If we find this, we parse a query of the form "X : A".
       Otherwise we parse a query of the form "A".
    *)
    fun parseQuery' (f as LS.Cons ((L.ID (L.Upper, name), r), s')) =
          parseQuery1 (name, f, LS.expose s')
      | parseQuery' (f) =
          returnQuery (NONE, ParseTerm.parseTerm' f)

    (* parseQuery --- currently not exported *)
    fun parseQuery (s) = parseQuery' (LS.expose s)

    (* parseDefine4 parses the definition body *)
    (* "U" *)
    fun parseDefine4 (optName, optT, s) =
        let
          val (tm', f') = ParseTerm.parseTerm' (LS.expose s)
        in
          (ExtQuery.define (optName, tm', optT), f')
        end

    (* parseDefine3 parses the equal sign in a long form define *)
    (* "= U" *)
    fun parseDefine3 (optName, (tm, LS.Cons ((L.EQUAL, r), s'))) =
          parseDefine4 (optName, SOME(tm), s')
      | parseDefine3 (_, (tm, LS.Cons ((t, r), _))) =
          Parsing.error (r, "Expected `=', found " ^ L.toString t)

    (* parseDefine2 switches between short and long form *)
    (* ": V = U" | "= U" *)
    fun parseDefine2 (optName, LS.Cons ((L.COLON, r), s')) =
          parseDefine3 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | parseDefine2 (optName, LS.Cons ((L.EQUAL, r), s')) =
          parseDefine4 (optName, NONE, s')
      | parseDefine2 (_, LS.Cons ((t, r), _)) =
          Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)

    (* parseDefine1 parses the name of the constant to be defined *)
    (* "c : V = U" | "_ : V = U" | "c = U" | "_ = U" *)
    fun parseDefine1 (LS.Cons ((L.ID (idCase,name), r), s')) =
          parseDefine2 (SOME(name), LS.expose s')
      | parseDefine1 (LS.Cons ((L.UNDERSCORE, r), s')) =
          parseDefine2 (NONE, LS.expose s')
      | parseDefine1 (LS.Cons ((t, r), _)) =
          Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

    fun parseSolve3 (defns, nameOpt, LS.Cons ((L.COLON, r), s'), r0) =
        let
          val (tm, f' as LS.Cons ((_, r), _)) = ParseTerm.parseTerm' (LS.expose s')
        in
          ((List.rev defns, ExtQuery.solve (nameOpt, tm, P.join (r0, r))), f')
        end
      | parseSolve3 (_, _, LS.Cons ((t,r), s'), r0) =
          Parsing.error (r, "Expected `:', found " ^ L.toString t)

    fun parseSolve2 (defns, LS.Cons ((L.UNDERSCORE, r), s'), r0) =
          parseSolve3 (defns, NONE, LS.expose s', r0)
      | parseSolve2 (defns, LS.Cons ((L.ID (_, name), r), s'), r0) =
          parseSolve3 (defns, SOME name, LS.expose s', r0)
      | parseSolve2 (_, LS.Cons ((t,r), s'), r0) =
          Parsing.error (r, "Expected identifier or `_', found " ^ L.toString t)

    and parseSolve1 (defns, LS.Cons ((L.SOLVE, r0), s')) =
          parseSolve2 (defns, LS.expose s', r0)
      | parseSolve1 (defns, LS.Cons ((L.DEFINE, r0), s')) =
        let
          val (defn, f') = parseDefine1 (LS.expose s')
        in
          parseSolve1 (defn::defns, f')
        end
      | parseSolve1 (defns, LS.Cons((t, r), s)) =
          Parsing.error(r, "Expected %define or %solve, found " ^ L.toString t)

    and parseSolve' (f) = parseSolve1 (nil, f)

  in
    val parseQuery' = parseQuery'
    val parseSolve' = parseSolve'
  end  (* local ... in *)

end;  (* functor ParseQuery *)
