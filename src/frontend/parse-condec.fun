(* Parsing Signature Entries *) 
(* Author: Frank Pfenning *)

functor ParseConDec
  (structure Parsing' : PARSING
   structure ExtSyn' : EXTSYN
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing = Parsing'
     sharing ParseTerm.ExtSyn = ExtSyn')
     : PARSE_CONDEC =
struct

  structure Parsing = Parsing'
  structure ExtSyn = ExtSyn'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    (* parseConDec3  "U" *)
    fun parseConDec3 (optName, optTm, s) =
        let
	  val (tm', f') = ParseTerm.parseTerm' (LS.expose s)
	in
	  (ExtSyn.condef (optName, tm', optTm), f')
	end

    (* parseConDec2  "= U" | "" *)
    fun parseConDec2 (optName, (tm, LS.Cons((L.EQUAL, r), s'))) =
          parseConDec3 (optName, SOME(tm), s')
      | parseConDec2 (SOME(name), (tm, f)) =
	  (ExtSyn.condec (name, tm), f)
      | parseConDec2 (NONE, (tm, LS.Cons((t,r),s'))) =
	  Parsing.error (r, "Illegal anonymous declared constant")

    (* parseConDec1  ": V = U" | "= U" *)
    fun parseConDec1 (optName, LS.Cons ((L.COLON, r), s')) =
          parseConDec2 (optName, ParseTerm.parseTerm' (LS.expose s'))
      | parseConDec1 (optName, LS.Cons ((L.EQUAL, r), s')) =
	  parseConDec3 (optName, NONE, s')
      | parseConDec1 (optName, LS.Cons ((t,r), s')) =
	  Parsing.error (r, "Expected `:' or `=', found " ^ L.toString t)

    (* parseConDec' : lexResult front -> ExtSyn.ConDec * lexResult front
       Invariant: first token in exposed input stream is an identifier or underscore
    *)
    fun parseConDec' (LS.Cons ((L.ID (idCase,name), r), s')) =
          parseConDec1 (SOME(name), LS.expose s')
      | parseConDec' (LS.Cons ((L.UNDERSCORE, r), s')) =
	  parseConDec1 (NONE, LS.expose s')

    (* parseConDec --- currently not exported *)
    fun parseConDec (s) = parseConDec' (LS.expose s)
      
  in
    val parseConDec' = parseConDec'
  end  (* local ... in *)

end;  (* functor ParseConDec *)
