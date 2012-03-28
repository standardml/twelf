(* The Parser *)
(* Author: Richard Fontana *)

functor Parse  (structure DextSyn  : DEXTSYN
                structure Interface : INTERFACE
                structure Parserr : PARSERR
                     sharing type Parserr.arg = Interface.arg
                     sharing type Parserr.pos = Interface.pos
                     sharing type Parserr.result = DextSyn.Ast
                structure Tokens : Delphin_TOKENS
                     sharing type Tokens.token = Parserr.Token.token
                     sharing type Tokens.svalue = Parserr.svalue) : PARSE =

struct

structure DextSyn = DextSyn
structure Interface = Interface
structure Parserr = Parserr
structure Tokens = Tokens
structure Streamm = Parserr.Streamm
structure Token = Parserr.Token

(* Given a lexer, invoke parser *)
fun invoke lexstream =
   Parserr.parse(0, lexstream, Interface.error, Interface.nothing)

(* Parse a named input file *)
fun fparse fname =
   let val _ = Interface.init_line ()
       val infile = TextIO.openIn(fname)
       val lexer = Parserr.makeLexer
           (fn _ => Compat.inputLine97 infile)
       val empty = !Interface.line
       val dummyEOF = Tokens.EOF(empty, empty)
       fun loop lexer =
           let val (result, lexer) = invoke lexer
               val (nextToken, lexer) = Parserr.Streamm.get lexer
           in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then ()
              else loop lexer;
              (* DextSyn.printAst result; *)
              (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
             (* DextSyn.termparse result; *)
              ()
           end
   in loop lexer
   end


fun sparse () =
  let
    val _ = Interface.init_line ()
    val infile = TextIO.openString (TextIO.input TextIO.stdIn)
    val lexer = Parserr.makeLexer
           (fn _ => Compat.inputLine97 infile)
    val empty = !Interface.line
    val dummyEOF = Tokens.EOF(empty, empty)
    fun loop lexer =
      let val (result, lexer) = invoke lexer
          val (nextToken, lexer) = Parserr.Streamm.get lexer
       in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then (* () *)
                    result
              else loop lexer
       end
   in loop lexer
   end




fun  gparse fname =
   let val _ = Interface.init_line ()
       val infile = TextIO.openIn(fname)
       val lexer = Parserr.makeLexer
           (fn _ => Compat.inputLine97 infile)
       val empty = !Interface.line
       val dummyEOF = Tokens.EOF(empty, empty)
       fun loop lexer =
           let val (result, lexer) = invoke lexer
               val (nextToken, lexer) = Parserr.Streamm.get lexer
           in
              if Parserr.sameToken(nextToken, dummyEOF)
                 then (* () *)
                    result
              else loop lexer
              (* DextSyn.printAst result; *)
              (* Invoke the term parser on the Term nodes in the
                 generated syntax tree *)
             (* DextSyn.termparse result; *)
           (*   ()  *)
           end
   in loop lexer
   end
end  (* functor Parse *)


