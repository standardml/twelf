(* Parsing Define Declarations in Solve Queries *)
(* Author: Roberto Virga *)

functor ParseDefine
  (structure Paths : PATHS
   structure Parsing' : PARSING
     sharing Parsing'.Lexer.Paths = Paths
   structure ExtDefine' : EXTDEFINE
     sharing ExtDefine'.Paths = Paths
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing.Lexer = Parsing'.Lexer
     sharing ParseTerm.ExtSyn = ExtDefine'.ExtSyn)
     : PARSE_DEFINE =
struct
  structure Parsing = Parsing'
  structure ExtDefine = ExtDefine'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  
    structure P = Paths

    (* parseDefine4 parses the variable name *)
    fun parseDefine4 (name, optT, LS.Cons ((L.ID (L.Upper, var), r), s'), r0) =
          (ExtDefine'.define (name, optT, var, P.join(r0, r)), LS.expose s')
      | parseDefine4 (_, _, LS.Cons ((t, r), _), _) =
          Parsing.error (r, "Expected free uppercase variable, found " ^ L.toString t)
    
    (* parseDefine3 parses the equal sign in a long form define *)
    fun parseDefine3 (name, optT, LS.Cons ((L.EQUAL, r), s'), r0) =
          parseDefine4 (name, optT, LS.expose s', P.join (r0, r))
      | parseDefine3 (_, _, LS.Cons ((t, r), _), _) =
          Parsing.error (r, "Expected `=', found " ^ L.toString t)

    (* parseDefine2 switches between short and long form *)
    fun parseDefine2 (name, LS.Cons ((L.COLON, r), s'), r0) = (* long form *)
          let
            val (t, f') = ParseTerm.parseTerm' (LS.expose s')
          in
            parseDefine3 (name, SOME (t), f', r0)
          end
      | parseDefine2 (name, LS.Cons ((L.EQUAL, r), s'), r0) = (* short form *)
          parseDefine4 (name, NONE, LS.expose s', P.join (r0, r))
      | parseDefine2 (_, LS.Cons ((t, r), _), _) =
          Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)

    (* parseDefine1 parses the name of the constant to be defined *)
    fun parseDefine1 (LS.Cons ((L.ID (L.Lower, name), r), s')) =
          parseDefine2 (name, LS.expose s', r)
      | parseDefine1 (LS.Cons ((t, r), _)) =
          Parsing.error (r, "Expected lowercase constant identifier, found " ^ L.toString t)

    (* parseDefine' : lexResult front -> define * lexResult front
       Invariant: exposed input stream starts with DEFINE
    *)
    fun parseDefine' (LS.Cons ((L.DEFINE, r), s')) = parseDefine1 (LS.expose s')
  in
    val parseDefine' = parseDefine'
  end  (* local *)

end;  (* functor ParseDefine *)
