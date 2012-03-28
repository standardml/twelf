(* Parsing Fixity and Name Preference Declarations *)
(* Author: Frank Pfenning *)

functor ParseFixity
  ((*! structure Parsing' : PARSING !*)
   structure Names' : NAMES)
     : PARSE_FIXITY =
struct

  (*! structure Parsing = Parsing' !*)
  structure Names = Names'

  local
    (* some shorthands *)
    structure L = Lexer
    structure LS = Lexer.Stream
    structure FX = Names.Fixity

    fun fixToString (FX.Strength(p)) = Int.toString p

    (* idToPrec (region, (idCase, name)) = n
       where n is the precedence indicated by name, which should consists
       of all digits.  Raises error otherwise, or if precedence it too large
    *)
    fun idToPrec (r, (_, name)) =
      let val prec = FX.Strength (L.stringToNat (name))
                     handle Overflow => Parsing.error (r, "Precedence too large")
                          | L.NotDigit _ => Parsing.error (r, "Precedence not a natural number")
      in
        if FX.less(prec, FX.minPrec) orelse FX.less (FX.maxPrec, prec)
          then Parsing.error (r, "Precedence out of range ["
                              ^ fixToString FX.minPrec ^ ","
                              ^ fixToString FX.maxPrec ^ "]")
        else prec
      end

    (*-----------------------------*)
    (* Parsing fixity declarations *)
    (*-----------------------------*)

    (* parseFixCon "id" *)
    fun parseFixCon (fixity, LS.Cons ((L.ID (_, name), r), s')) =
        (((Names.Qid (nil,name),r), fixity), LS.expose s')
      | parseFixCon (fixity, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected identifier to assign fixity, found " ^ L.toString t)

    (* parseFixPrec "n id" where n is precedence *)
    fun parseFixPrec (fixity, LS.Cons ((L.ID id, r), s')) =
          parseFixCon (fixity (idToPrec (r, id)), LS.expose s')
      | parseFixPrec (fixity, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected precedence, found " ^ L.toString t)

    (* parseInfix "none|left|right n id" where n is precedence *)
    fun parseInfix (LS.Cons ((L.ID (L.Lower, "none"), r), s')) =
          parseFixPrec ((fn p => FX.Infix(p, FX.None)), LS.expose s')
      | parseInfix (LS.Cons ((L.ID (L.Lower, "left"), r), s')) =
          parseFixPrec ((fn p => FX.Infix(p, FX.Left)), LS.expose s')
      | parseInfix (LS.Cons ((L.ID (L.Lower, "right"), r), s')) =
          parseFixPrec ((fn p => FX.Infix(p, FX.Right)), LS.expose s')
      | parseInfix (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected associatitivy `left', `right', or `none', found "
                            ^ L.toString t)

    (* parsePrefix "n id" where n is precedence *)
    fun parsePrefix (f) = parseFixPrec (FX.Prefix, f)

    (* parsePostfix "n id" where n is precedence *)
    fun parsePostfix (f) = parseFixPrec (FX.Postfix, f)

    (* parseFixity' : lexResult stream -> (name,fixity) * lexResult stream
       Invariant: token stream starts with %infix, %prefix or %postfix
    *)
    fun parseFixity' (LS.Cons ((L.INFIX, r), s')) = parseInfix (LS.expose s')
      | parseFixity' (LS.Cons ((L.PREFIX, r), s')) = parsePrefix (LS.expose s')
      | parseFixity' (LS.Cons ((L.POSTFIX, r), s')) = parsePostfix (LS.expose s')
      (* anything else should be impossible *)

    fun parseFixity (s) = parseFixity' (LS.expose (s))

    (*------------------------------------*)
    (* Parsing name preferences %name ... *)
    (*------------------------------------*)

    (* parseName5 "string ... )" or ")" *)
    fun parseName5 (name, r0, prefENames, prefUNames, LS.Cons ((L.ID (_, prefUName), r), s')) =
        (* prefUName should be lower case---not enforced *)
        parseName5 (name, r0, prefENames, prefUNames @ [prefUName] , LS.expose s')
      | parseName5 (name, r0, prefENames, prefUNames, LS.Cons ((L.RPAREN, r), s')) =
        (((Names.Qid (nil, name), r0), (prefENames, prefUNames)), LS.expose s')
      | parseName5 (name, r0, prefENames, prefUNames, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected name preference or ')', found " ^ L.toString t)

    (* parseName3 "string" or "" *)
    fun parseName3 (name, r0, prefEName, LS.Cons ((L.ID (_, prefUName), r), s')) =
        (* prefUName should be lower case---not enforced *)
        (((Names.Qid (nil, name), r0), (prefEName, [prefUName])), LS.expose s')
      | parseName3 (name, r0, prefEName, LS.Cons ((L.LPAREN, r), s')) =
        parseName5 (name, r0, prefEName, nil, LS.expose s')
      | parseName3 (name, r0, prefEName, f) =
        (((Names.Qid (nil, name), r0), (prefEName, nil)), f)

    (* parseName4 "string ... )" or ")" *)
    fun parseName4 (name, r0, prefENames, LS.Cons ((L.ID (_, prefEName), r), s')) =
        if L.isUpper prefEName
          then parseName4 (name, r0,  prefENames @ [prefEName] , LS.expose s')
        else Parsing.error (r, "Expected uppercase identifer, found " ^ prefEName)
      | parseName4 (name, r0, prefENames, LS.Cons ((L.RPAREN, r), s')) =
          parseName3 (name, r0, prefENames, LS.expose s')
      | parseName4 (name, r0, prefENames, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected name preference or ')', found " ^ L.toString t)

    (* parseName2 "string" or "string string"
              or "(string ... ) string"  or " string (string ...)"
              or "(string ... ) (string ...)" *)
    fun parseName2 (name, r0, LS.Cons ((L.ID (_, prefEName), r), s')) =
        if L.isUpper prefEName
          then parseName3 (name, r0, [prefEName], LS.expose s')
        else Parsing.error (r, "Expected uppercase identifer, found " ^ prefEName)
      | parseName2 (name, r0, LS.Cons ((L.LPAREN, r), s')) =
        parseName4 (name, r0, nil, LS.expose s')
      | parseName2 (name, r0, LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected name preference, found " ^ L.toString t)

    (* parseName1 "id string" or "id string string" *)
    fun parseName1 (LS.Cons ((L.ID (_, name), r), s')) =
          parseName2 (name, r, LS.expose s')
      | parseName1 (LS.Cons ((t, r), s')) =
          Parsing.error (r, "Expected identifer to assign name preference, found " ^ L.toString t)

    (* parseNamePref' "%name id string" or "%name id string string"
       Invariant: token stream starts with %name
    *)
    fun parseNamePref' (LS.Cons ((L.NAME, r), s')) = parseName1 (LS.expose s')

    fun parseNamePref (s) = parseNamePref' (LS.expose s)

  in
    val parseFixity' = parseFixity'
    val parseNamePref' = parseNamePref'
  end  (* local ... in *)

end;  (* functor ParseFixity *)
