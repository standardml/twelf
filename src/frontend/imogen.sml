
signature IMOGEN_DEC =
   sig
      type dec 
      val mkDec : string -> dec
   end

structure ImogenDec : IMOGEN_DEC =
   struct
      type dec = string
      fun mkDec x = x
   end

signature PARSE_IMOGEN =
   sig
      val parseImogen' : string Parsing.parser
   end

structure ParseImogen :> PARSE_IMOGEN =
   struct

      structure P = Parsing
      structure S = P.Stream
      structure L = Lexer

      exception Impossible

      fun parseImogen' S.Empty = raise Impossible 
        | parseImogen' (S.Cons((L.IMOGEN, _), s)) =
          let in 
             case S.expose s of 
                S.Empty => raise Impossible 
              | (S.Cons ((L.ID (_, id), _), s)) => (id, S.expose s)
              | _ => raise Impossible
          end
        | parseImogen' _ = raise Impossible 

   end
