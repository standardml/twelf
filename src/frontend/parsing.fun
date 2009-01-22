functor Parsing
  (structure Stream' : STREAM
   (*! structure Lexer' : LEXER !*)
   (*! sharing Lexer'.Stream = Stream' !*)
     )
     : PARSING =
struct

  structure Stream = Stream'
  (*! structure Lexer = Lexer' !*)

  type lexResult = Lexer.Token * Paths.region

  type 'a parser = lexResult Stream.front -> 'a * lexResult Stream.front

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

end;  (* functor Parsing *)

structure Parsing =
  Parsing (structure Stream' = Stream
	   (*! structure Lexer' = Lexer !*)
	     );
