
signature PARSE_IMOGEN_ARGS =
   sig
      structure ParseTerm: PARSE_TERM
      structure ReconConDec: RECON_CONDEC
      sharing ParseTerm.ExtSyn = ReconConDec.ExtSyn 
   end

functor ParseImogenFn(Args: PARSE_IMOGEN_ARGS) : PARSE_IMOGEN =
struct

open Args
structure P = Parsing
structure S = P.Stream
structure L = Lexer
structure I = Imogen

exception Impossible

fun parseImogen' (S.Cons((L.IMOGEN, r), s)) =
    let 
       val (term, s') = ParseTerm.parseTerm' (S.expose s) 
       val condec = ReconConDec.condec("imogen", term)
       val loc = Paths.Loc("dummy", r)
       val (rdec, _) = ReconConDec.condecToConDec(condec, loc, false)
    in 
       case rdec of 
          NONE => raise Impossible 
        | SOME d => (I.ConDec d, s')
    end
  | parseImogen' _ = raise Impossible 

end
