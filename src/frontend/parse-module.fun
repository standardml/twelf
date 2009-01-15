(* Parsing modules *)
(* Author: Kevin Watkins *)

functor ParseModule
  ((*! structure Paths : PATHS !*)
   (*! structure Parsing' : PARSING !*)
   (*! sharing Parsing'.Lexer.Paths = Paths !*)
   structure ModExtSyn' : MODEXTSYN
   (*! sharing ModExtSyn'.Paths = Paths !*)
   structure ParseTerm : PARSE_TERM
   (*! sharing ParseTerm.Lexer = Parsing'.Lexer !*)
     sharing ParseTerm.ExtSyn = ModExtSyn'.ExtSyn)
  : PARSE_MODULE =
struct

  (*! structure Parsing = Parsing' !*)
  structure ModExtSyn = ModExtSyn'

  structure L = Lexer
  structure LS = Lexer.Stream  
  structure E = ModExtSyn

  fun parseLBrace'(LS.Cons ((L.LBRACE, _), s')) = ((), LS.expose s')
    | parseLBrace'(LS.Cons ((t, r), _)) = Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseEqual'(LS.Cons ((L.EQUAL, _), s')) = ((), LS.expose s')
    | parseEqual'(LS.Cons ((t, r), _)) = Parsing.error (r, "Expected `=', found token " ^ L.toString t)

  fun parseColonEqual' (LS.Cons ((L.COLON, r1), s')) =
      (case LS.expose s'
         of LS.Cons ((L.EQUAL, _), s'') => ((), LS.expose s'')
          | LS.Cons ((t, r2), s'') =>
              Parsing.error (r2, "Expected `=', found token " ^ L.toString t))
    | parseColonEqual' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `:=', found token " ^ L.toString t)

  fun parseDot' (LS.Cons ((L.DOT, r), s')) = (r, LS.expose s')
    | parseDot' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `.', found token " ^ L.toString t)

  fun parseMorph' (f as LS.Cons ((L.ID _, r0), _)) =
      let
          val ((ids, (L.ID (_, id), r1)), f') = ParseTerm.parseQualId' f
      in
         (E.morstr(ids, id, Paths.join (r0, r1)), f')
      end
    | parseMorph' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t)

  fun parseConInst' (f as LS.Cons ((L.ID _, r0), _)) =
      let
        val ((ids, (L.ID (_, id), r1)), f1) = ParseTerm.parseQualId' (f)
        val (_, f2) = parseColonEqual' (f1)
        val (tm, f3) = ParseTerm.parseTerm' (f2)
        val (r2, f4) = parseDot' (f3)
      in
        (E.coninst ((ids, id, Paths.join (r0, r1)), (tm, Paths.join (r0, r2))),
         f4)
      end
    | parseConInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  fun parseStrInst2' (r0, f as LS.Cons ((L.ID _, r1), _)) =
      let
        val ((ids, (L.ID (_, id), r2)), f1) = ParseTerm.parseQualId' (f)
        val (_, f2) = parseColonEqual' (f1)
        val (mor, f3) = parseMorph' (f2)
        val (r3, f4) = parseDot' (f3)
      in
        (E.strinst ((ids, id, Paths.join (r1, r2)),
                    (mor, Paths.join (r0, r3))),
         f4)
      end
    | parseStrInst2' (r0, LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t)

  fun parseStrInst' (LS.Cons ((L.STRUCT, r), s')) =
        parseStrInst2' (r, LS.expose s')
    | parseStrInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `%struct', found token " ^ L.toString t)

  fun parseInsts' (f as LS.Cons ((L.ID _, _), _)) =
      let
        val (inst, f') = parseConInst' (f)
        val (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (f as LS.Cons ((L.STRUCT, _), _)) =
      let
        val (inst, f') = parseStrInst' (f)
        val (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (LS.Cons ((L.RBRACE, _), s')) =
        (nil, LS.expose s')
    | parseInsts' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier or `%struct', found token " ^ L.toString t)

  fun parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) =
        parseInsts' (LS.expose s')
    | parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseSigBegin' (LS.Cons ((L.SIG, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), r), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.sigbegin id, f')
          end 
        | LS.Cons ((t, r), s') =>
	  Parsing.error (r, "Expected signature identifier, found token " ^ L.toString t)

  fun parseStrDec' (LS.Cons ((L.STRUCT, r), s')) =
     case LS.expose s'
        of LS.Cons ((L.ID (_, id), r1), s1') => (
           case LS.expose s1'
              of LS.Cons ((L.COLON, r2), s2') =>
                 let
                     val f' = LS.expose s2'
                     val ((domids, (L.ID (_, domid), r3)), f') = ParseTerm.parseQualId' (f')
                     val (_, f') = parseEqual' (f')
                     val (insts, f') = parseInstantiate'(f')
                  in
                     (* don't know what to put instead of r3 -fr *)
                     (E.strdec(id, (domids @ [domid], r3), insts), f')
                  end
               | LS.Cons ((L.EQUAL, r2), s2') =>
                 let
                    val (mor, f') = parseMorph' (LS.expose s2')
                 in
                    (* don't know what to put instead of r2 -fr *)
                    ((E.strdef (id, (mor, r2))), f')
                 end
               | LS.Cons ((t, r), s') =>
                 Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)
         )
         | LS.Cons ((t, r), s') =>
           Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t)

  (* ignoring these two tokens *)
  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) = ((), LS.expose s')
  fun parseOpen' (LS.Cons ((L.OPEN, r), s')) = ((), LS.expose s')

end
