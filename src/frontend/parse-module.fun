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

  fun parseSingleToken' token f' : Paths.region * Front =
     let
     	val LS.Cons ((t, r), s') = f'
     in 
     	if t = token
     	then (r, LS.expose s')
        else Parsing.error (r, "Expected " ^ L.toString token ^ ", found token " ^ L.toString t)
     end
  val parseLBrace' = parseSingleToken'(L.LBRACE)
  val parseArrow' = parseSingleToken'(L.ARROW)
  val parseEqual' = parseSingleToken'(L.EQUAL)
  val parseColon' = parseSingleToken'(L.COLON)
  val parseDot' = parseSingleToken'(L.DOT)
  
  fun parseId'(LS.Cons((L.ID(_,id),r), s')) = ((id,r), LS.expose s')
    | parseId'(LS.Cons ((t, r), _)) =
     	Parsing.error (r, "Expected unqualified identifier, found token " ^ L.toString t)

  fun parseQualId'(f') : ID * Front =
    let
       val ((ids, (L.ID (_, id), r)), f' as LS.Cons((_,r'),s')) = ParseTerm.parseQualId' (f')
    in
       ((ids @ [id], Paths.join(r, r')), f')
    end

  fun parseIDList'(f' as LS.Cons ((L.ID _, _), _)) =
      let
          val (id, f') = parseQualId' f'
          val (rest, f') = parseIDList'(f')
      in
         (id :: rest, f')
      end
    | parseIDList'(f') = (nil, f')

  fun parseSign'(f' as LS.Cons ((t, r), _)) = parseIDList' f' (* empty list is allowed *)

  fun parseMorph'(f' as LS.Cons ((t, r), _)) = case parseIDList' f'
    of (nil, _) => Parsing.error (r, "Expected structure or view identifier, found token " ^ L.toString t)
     | mf => mf
  
  fun parseRel'(f' as LS.Cons ((t, r), _)) = case parseIDList' f'
    of (nil, _) => Parsing.error (r, "Expected identifier, found token " ^ L.toString t)
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

  fun parseOpenIds'(f' as LS.Cons((L.DOT,_),_)) = (nil,f')
    | parseOpenIds'(f' as LS.Cons((L.ID(_,_),_),_)) =
     let
     	val (old as (oldl,oldr), f') = parseQualId' f'
     	val (new, f') = case f'
     	   of LS.Cons((L.AS, _), s') => parseId' (LS.expose s')
     	    | LS.Cons((L.ID(_,_),_), _) => ((List.last oldl, oldr), f')
     	    | LS.Cons((L.DOT,_), _) => ((List.last oldl, oldr), f')
     	    | LS.Cons((t, r), _) =>
     	       Parsing.error (r, "Expected qualified identifier, found token " ^ L.toString t)
     	val (rest, f') = parseOpenIds' f'
      in
      	 ((old, new) :: rest, f')
      end
    | parseOpenIds' (LS.Cons ((t, r), _)) =
        Parsing.error (r, "Expected `.' or qualified identifier', found token " ^ L.toString t)

  fun parseOpen'(f' as LS.Cons((L.DOT,_),_)) = (nil, f')
    | parseOpen'(f' as LS.Cons((L.OPEN,_),s')) =
        let val (opens, f') = parseOpenIds' (LS.expose s')
        in (opens, f')
        end
    | parseOpen'(LS.Cons ((t, r), s')) = Parsing.error (r, "Expected `%open' or `.', found token " ^ L.toString t)

  (* parses a %include declaration in a signature (special case: %meta) *)
  fun parseIncludeOrMeta' (s', isMeta) = 
     let
        val (id, f') = parseQualId'(LS.expose s')
	     val (opdec, f') = parseOpen' f'
     in
       (E.sigincl (id, isMeta, opdec), f')
     end 
  fun parseInclude' (LS.Cons ((L.INCLUDE, r), s')) = parseIncludeOrMeta'(s', false)
    | parseInclude' (LS.Cons ((L.META, r), s')) = parseIncludeOrMeta'(s', true)

  (* parses a %include declaration in a link *)
  fun parseInclInst' (LS.Cons ((L.INCLUDE, r), s')) =
     let
        val (mor, f') = parseMorph'(LS.expose s')
        val (r', f') = parseDot' (f')
     in
       (E.inclinst (mor, Paths.join(r,r')), f')
     end 
  
  fun parseConCase'(f' as LS.Cons ((L.ID _, r0), _)) =
      let
         val (con, f') = parseQualId'(f')
         val (_, f') = parseColon'(f')
         val (_, f') = parseEqual'(f')
         val (tm, f') = ParseTerm.parseTerm'(f')
         val (r2, f') = parseDot' (f')
      in
        (E.concase (con, (tm, Paths.join (r0, r2))), f')
      end

  (* parses a %struct case in a logical relation *)
  fun parseStrCase' (LS.Cons ((L.STRUCT, r), s')) =
     let
        val (id, f') = parseQualId'(LS.expose s')
        val (_,f') = parseColon' f'
        val (_,f') = parseEqual' f'
        val (rel, f') = parseRel' f'
        val (r2, f') = parseDot' (f')
     in
       (E.strcase (id, (rel, Paths.join (r, r2))), f')
     end

  (* parses a %include declaration in a logical relation *)
  fun parseInclCase' (LS.Cons ((L.INCLUDE, r), s')) =
     let
        val (rel, f') = parseRel'(LS.expose s')
        val (r', f') = parseDot' (f')
     in
       (E.inclcase (rel, Paths.join(r,r')), f')
     end 

  (* parses a list of symbol instantiations (used for structures) *)
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
    | parseInsts' (f as LS.Cons ((L.INCLUDE, _), _)) =
      let
        val (inst, f') = parseInclInst' (f)
        val (insts, f'') = parseInsts' (f')
      in
        (inst::insts, f'')
      end
    | parseInsts' (LS.Cons ((L.RBRACE, _), s')) =
        (nil, LS.expose s')
    | parseInsts' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected identifier, `%struct', `%include', or `}', found token " ^ L.toString t)
    
  (* parses the {...} part of a structure declaration *)
  fun parseInstantiate' (f as LS.Cons ((L.LBRACE, _), s')) = parseInsts'(LS.expose s')
    | parseInstantiate' (LS.Cons ((t, r), s')) =
        Parsing.error (r, "Expected `{', found token " ^ L.toString t)

  fun parseImplicit(LS.Cons ((L.IMPLICIT, _), s')) = (true, LS.expose s')
    | parseImplicit(f') = (false, f')
  fun parseStrDec' (LS.Cons ((L.STRUCT, r0), s')) =
  let
     val (implicit, f') = parseImplicit (LS.expose s')
  in
     case f'
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
	             val (opdec, f') = parseOpen' f'
                  in
                     (E.strdec(id, dom, insts, opdec, implicit), f')
                  end
               | LS.Cons ((L.EQUAL, r2), s2') =>
                 let
                    val (mor, f' as LS.Cons((_,r3),_)) = parseMorph' (LS.expose s2')
                 in
                    ((E.strdef (id, (mor, Paths.join(r2,r3)), implicit)), f')
                 end
               | LS.Cons ((t, r), s') =>
                 Parsing.error (r, "Expected `:' or `=', found token " ^ L.toString t)
         )
         | LS.Cons ((t, r), s') =>
           Parsing.error (r, "Expected `%implicit' or new identifier, found token " ^ L.toString t)
  end

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
  let
     val (implicit, f') = parseImplicit (LS.expose s')
  in
     case f'
       of LS.Cons ((L.ID (_, id), r1), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseColon' (f')
             val (dom, f') = parseQualId' (f')
             val (_, f') = parseArrow'(f')
             val (cod, f') = parseSign' (f')
             val (_, f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.viewbegin(id, dom, cod, implicit), f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r1, "Expected new module identifier, found token " ^ L.toString t)
  end
  
  fun parseRelBegin' (LS.Cons ((L.REL, r), s')) =
     case LS.expose s'
       of LS.Cons ((L.ID (_, id), _), s') =>
          let
             val f' = LS.expose s'
             val (_, f') = parseColon' (f')
             fun parseMorphs(f') =
                   let val (mor, f') = parseMorph' f'
                   in
                       case f'
                         of LS.Cons((L.ARROW,_),s') =>
                            let val (mors, f') = parseMorphs (LS.expose s')
                            in (mor::mors, f')
                            end
                          | _ => ([mor], f')
                    end
             val (mors, f') = parseMorphs (f')
             val (r', f') = parseEqual' (f')
             val (_, f') = parseLBrace' (f')
          in
             (E.relbegin(id, mors, Paths.join(r,r')), f')
          end 
        | LS.Cons ((t, r1), s') =>
	  Parsing.error (r1, "Expected new module identifier, found token " ^ L.toString t)
  
  fun parseRead' (f as LS.Cons ((L.READ, _), s')) =
     case LS.expose s'
        of LS.Cons ((L.STRING name, r), s') => (E.readfile name, LS.expose s')
         | LS.Cons ((t, r1), s') =>
           Parsing.error (r1, "Expected string, found token " ^ L.toString t)

  fun parseNamespaceURI'(pOpt, r, LS.Cons ((L.STRING ns, r'), s')) =
      let val ns' = URI.parseURI (String.substring(ns, 1, String.size ns - 2)) (* remove quotes *)
          handle URI.Error(msg) => raise Parsing.error(r', msg)
          val _ = if isSome (#query ns') orelse isSome (#fragment ns')
                  then Parsing.error(r', "namespace URI may not have query (?) or fragment (#)")
                  else ()
      in (E.namespace(pOpt, ns', Paths.join(r,r')), LS.expose s')
      end
    | parseNamespaceURI'(_, _, LS.Cons ((t, r), s')) = Parsing.error (r, "Expected string, found token " ^ L.toString t)
  fun parseNamespace' (f as LS.Cons ((L.NAMESPACE, r), s')) =
     case LS.expose s'
        of f' as LS.Cons ((L.ID(_, id), _), s') =>
           let val (_, f') = parseEqual' (LS.expose s')
           in parseNamespaceURI'(SOME id, r, f')
           end
         | f' => parseNamespaceURI'(NONE, r, f')

end
