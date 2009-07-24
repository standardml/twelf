
structure Imogen =
struct 

structure Stream = Parser.Stream

val msg = "Imogen 1.0"

(* datatype decl = ConDec of string *  *)

val parse : string -> (Parser.fileParseResult * Paths.region) list =
 fn s => 
    let
       val f = TextIO.openIn s
    in
       let in 
          Stream.toList(Parser.parseStream f)
          before TextIO.closeIn f
       end handle exn => 
                  let in 
                     TextIO.closeIn f 
                   ; raise exn
                  end
    end

end


(* 

structure P = Parser
structure L = Lexer
structure S = Parser.Stream

S.take(Parser.parseStream (TextIO.openIn "test/nat.elf"), 5)
S.toList(Parser.parseStream (TextIO.openIn "test/nat.elf"))
Scratch.parse "test/fol-test.elf"

Server.server("",[])
OS.FileSys.chDir "test"

val f = TextIO.openIn "test/nat.elf"
val xs = L.lexStream f

val (x, xs) = case S.expose xs of 
                   S.Cons (x, xs) => (x, xs)
                 | _ => raise Fail ""

S.toList xs

val r = Scratch.parse "test/nat.elf"
S.toList r
S.expose r

Twelf.Config.read "test/sources.cfg";

*) 
