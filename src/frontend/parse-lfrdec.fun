(* Parsing LFR Signature Entries *)
(* Author: William Lovas *)
(* Based heavily on parse-condec.fun *)

functor ParseLFRDec
  (structure ExtLFRDec' : EXTLFRDEC
   structure ParseTerm : PARSE_TERM
     sharing ParseTerm.ExtSyn = ExtLFRDec'.ExtSyn)
  : PARSE_LFRDEC =
struct
  structure ExtLFRDec = ExtLFRDec'

  local

    structure L = Lexer
    structure LS = Lexer.Stream

    (*
 (* NB: old parsing code for s << a :: L.  resurrect someday? -wjl 9-25-2009 *)
    (* parseLFRSortDec2  ":: V" *)
    fun parseLFRSortDec2 (name, name', LS.Cons ((L.COLONCOLON, r), s')) =
            let val (tm, f') = ParseTerm.parseTerm' (LS.expose s')
            in
                (ExtLFRDec.sortdec (name, name', tm), f')
            end
      | parseLFRSortDec2 (name, name', LS.Cons ((t, r), s')) =
            Parsing.error (r, "Expected `::', found " ^ L.toString t)

    (* parseLFRSortDec1  "a :: V" *)
    fun parseLFRSortDec1 (name, LS.Cons ((L.ID (idCase', name'), r), s')) =
            parseLFRSortDec2 (name, name', LS.expose s')
      | parseLFRSortDec1 (name, LS.Cons ((t, r), s')) =
            Parsing.error (r, "Expected identifier, found " ^ L.toString t)
    *)

    fun parseLFRSortDec (name, LS.Cons ((L.ID (idCase', name'), r_name'), s')) =
            (ExtLFRDec.sortdec (name, (name', r_name')), LS.expose s')
      | parseLFRSortDec (name, LS.Cons ((t, r), s')) =
            Parsing.error (r, "Expected identifier, found " ^ L.toString t)

    fun parseLFRSubDec ((name, r_name), LS.Cons ((L.ID (idCase', name'), r_name'), s')) =
            (ExtLFRDec.subdec ((name, r_name), (name', r_name')), LS.expose s')
      | parseLFRSubDec ((name, r_name), LS.Cons ((t, r), s')) =
            Parsing.error (r, "Expected identifier, found " ^ L.toString t)

    (* parseLFRDec1  ":: V" | "<< a " | "<: s" *)
    (* invariant: first remaining token is a `::', a `<<', or a `<:' *)
    fun parseLFRDec1 ((name, r_name), LS.Cons ((L.COLONCOLON, r), s')) =
            let val (tm, f') = ParseTerm.parseTerm' (LS.expose s')
            in
                (ExtLFRDec.condec ((name, r_name), tm), f')
            end
      | parseLFRDec1 ((name, r_name), LS.Cons ((L.REFINES, r), s')) =
            (* drop r_name -- this is a defining declaration *)
            parseLFRSortDec (name, LS.expose s')
      | parseLFRDec1 ((name, r_name), LS.Cons ((L.SUBSORT, r), s')) =
            parseLFRSubDec ((name, r_name), LS.expose s')
      | parseLFRDec1 ((name, r_name), LS.Cons ((t, r), s')) =
            Parsing.error (r, "Expected `::', `<<', or `<:', found " ^ L.toString t ^ " (bug?)")

    (* invariant: first token is a constant, second token is a `::', a `<<',
       or a `<:' *)
    fun parseLFRDec' (LS.Cons ((L.ID (idCase, name), r), s')) =
            parseLFRDec1 ((name, r), LS.expose s')
      | parseLFRDec' (LS.Cons ((t, r), s')) =
            Parsing.error (r, "Constant expected, found token " ^ L.toString t ^ " (bug?)")

  in
    val parseLFRDec' = parseLFRDec'
  end (* local ... in *)
end;  (* functor ParseLFRDec *)
