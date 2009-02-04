(* Parsing modules *)
(* Author: Keven Watkins *)
(* Redesigned: Florian Rabe, Jan 09 *)

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

  type ID = string list * Paths.region
  type Front = (L.Token * Paths.region) LS.front

  fun parseSingleToken' (token, ascii) f' : Paths.region * Front =
     let
     	val LS.Cons ((t, r), s') = f'
     in 
     	if t = token
     	then (r, LS.expose s')
        else Parsing.error (r, "Expected `" ^ ascii ^ "', found token " ^ L.toString t)
     end
  val parseLBrace' = parseSingleToken'(L.LBRACE, "{")
  val parseArrow' = parseSingleToken'(L.ARROW, "->")
  val parseEqual' = parseSingleToken'(L.EQUAL, "=")
  val parseColon' = parseSingleToken'(L.COLON, ":")
  val parseDot' = parseSingleToken'(L.DOT, ".")
  
  fun parseQualId'(f') : ID * Front =
    let
       val ((ids, (L.ID (_, id), r)), f' as LS.Cons((_,r'),s')) = ParseTerm.parseQualId' (f')
    in
       ((ids @ [id], Paths.join(r, r')), f')
    end

  fun parseMorphAux'(f' as LS.Cons ((L.ID _, _), _)) =
      let
          val (id, f') = parseQualId' f'
          val (rest, f') = parseMorphAux'(f')
      in
         (id :: rest, f')
      end
    | parseMorphAux'(f') = (nil, f')

  fun parseMorph'(f' as LS.Cons ((t, r), _)) = case parseMorphAux' f'
    of (nil, _) => Parsing.error (r, "Expected structure or view identifier, found token " ^ L.toString t)
     | mf => mf
  
  fun parseConInst' (f' as LS.Cons ((L.ID _, r0), _)) =
      let
         val (con, f') = parseQualId'(f')
         val (_, f') = parseColon'(f')
         val (_, f') = parseEqual'(f')
         val (tm, f') = ParseTerm.parseTerm'(f')
         val (r2, f') = parseDot' (f')
      in
        (E.coninst (con, (tm, Paths.join (r0, r2))), f')
      end
    | parseConInst' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, found token " ^ L.toString t)

  fun parseStrInst2' ( f' as LS.Cons ((L.ID _, r), _)) =
      let
         val (str, f') = parseQualId' (f')
         val (_, f') = parseColon' (f')
         val (_, f') = parseEqual' (f')
         val (mor, f') = parseMorph' (f')
         val (r3, f') = parseDot' (f')
      in
        (E.strinst (str, (mor, Paths.join (r, r3))), f')
      end
    | parseStrInst2' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected structure identifier, found token " ^ L.toString t)

  fun parseStrInst' (LS.Cons ((L.STRUCT, _), s')) =
        parseStrInst2' (LS.expose s')
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
        Parsing.error (r, "Expected identifier, `%struct', or `}', found token " ^ L.toString t)

  fun parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) =
        parseInsts' (LS.expose s')
    | parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseSigBegin' (LS.Cons ((L.SIG, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), r1), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.sigbegin id, f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r, "Expected new module identifier, found token " ^ L.toString t)

  fun parseViewBegin' (LS.Cons ((L.VIEW, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), r1), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseColon' (f')
             val (dom, f') = parseQualId' (f')
             val (_, f') = parseArrow'(f')
             val (cod, f') = parseQualId' (f')
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.viewbegin(id, dom, cod), f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r1, "Expected new module identifier, found token " ^ L.toString t)

  fun parseQualIdList'(f' as LS.Cons((L.DOT, _), _)) = (nil, f')
    | parseQualIdList'(f') =
       let
          val (id, f') = parseQualId' f'
	  val (ids, f') = parseQualIdList' f'
       in
          (id :: ids, f')
       end

  fun parseOpen'(f' as LS.Cons((L.DOT,_),_)) = (nil, f')
    | parseOpen'(f' as LS.Cons((L.OPEN,_),s')) = parseQualIdList' (LS.expose s')
    | parseOpen'(LS.Cons ((t, r), s')) =
             Parsing.error (r, "Expected `%open' or `.', found token " ^ L.toString t)

  fun parseStrDec' (LS.Cons ((L.STRUCT, r0), s')) =
     case LS.expose s'
        of LS.Cons ((L.ID (_, id), r1), s1') => (
           case LS.expose s1'
              of LS.Cons ((L.COLON, r2), s2') =>
                 let
                     val f' = LS.expose s2'
                     val (dom,f') = parseQualId'(f')
                     val (insts, f') = case f'
                         of LS.Cons((L.DOT,_),_) => (nil, f')
			  | LS.Cons((L.OPEN,_),_) => (nil, f')
                          | _ => parseInstantiate'(#2 (parseEqual' f'))
	             val (ids, f') = parseOpen' f'
                  in
                     (E.strdec(id, dom, insts, ids), f')
                  end
               | LS.Cons ((L.EQUAL, r2), s2') =>
                 let
                    val (mor, f' as LS.Cons((_,r3),_)) = parseMorph' (LS.expose s2')
                 in
                    ((E.strdef (id, (mor, Paths.join(r2,r3)))), f')
                 end
               | LS.Cons ((t, r), s') =>
                 Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)
         )
         | LS.Cons ((t, r), s') =>
           Parsing.error (r, "Expected new identifier, found token " ^ L.toString t)

  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) =
     let
        val (id, f') = parseQualId'(LS.expose s')
	val (ids, f') = parseOpen' f'
     in
       (E.sigincl (id, ids), f')
     end 

  (* ignoring thistoken *)
  fun parseOpen' (LS.Cons ((L.OPEN, r), s')) = ((), LS.expose s')

end
