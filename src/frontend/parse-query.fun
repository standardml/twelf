(* Parsing Queries *) 
(* Author: Frank Pfenning *)

functor ParseQuery
  (structure Parsing' : PARSING
   structure ExtSyn' : EXTSYN
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.Parsing.Lexer = Parsing'.Lexer
     sharing ParseTerm.ExtSyn = ExtSyn')
  : PARSE_QUERY =
struct

  structure Parsing = Parsing'
  structure ExtSyn = ExtSyn'

  local
    structure L = Parsing.Lexer
    structure LS = Parsing.Lexer.Stream  

    fun returnQuery (optName, (tm, f)) = (ExtSyn.query (optName, tm), f)

    (* parseQuery1 (name, f, f')   ": A" from f' or "V" from f. *)

    fun parseQuery1 (name, f, LS.Cons ((L.COLON, r), s')) =
          returnQuery (SOME(name), ParseTerm.parseTerm' (LS.expose s'))
      | parseQuery1 (name, f, _) = returnQuery (NONE, ParseTerm.parseTerm' f)

    (* parseQuery' : lexResult front -> ExtSyn.query * lexResult front *)
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
      
  in
    val parseQuery' = parseQuery'
  end  (* local ... in *)

end;  (* functor ParseQuery *)
