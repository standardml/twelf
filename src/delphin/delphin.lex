structure Tokens = Tokens
structure Interface = Interface
structure Lexer = Lexer
open Interface

type pos = Interface.pos
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

val pos = ref 0
fun inc z = z := !z + 1
val eof = fn () => Tokens.EOF(!line, !line)


%%

%s COMMENT;

%header (functor DelphinLexFun(structure Tokens : Delphin_TOKENS
                               structure Interface : INTERFACE
                               structure Lexer : LEXER));

ws = [\ \t ];
uiden = (([#][A-Z][_])|[_A-Za-z])[-A-Za-z0-9!@#$/\^&*+|\\;'_]*([-A-Za-z0-9!@#/\^&*+|\\;'_]+)*;
catchall = .;

%%

<INITIAL,COMMENT>{ws}+          => (lex());
<INITIAL,COMMENT>\n             => (next_line(); lex());
<INITIAL>"(*"                   => (YYBEGIN COMMENT; lex());
<COMMENT>"*)"                   => (YYBEGIN INITIAL; lex());
<COMMENT>{catchall}             => (lex());
<INITIAL>"@"                    => (Tokens.AT(!line,!line));
<INITIAL>"*"                    => (Tokens.TIMES(!line,!line));
<INITIAL>"+"                    => (Tokens.PLUS(!line,!line));
<INITIAL>"::"                   => (Tokens.DBLCOLON(!line,!line));
<INITIAL>":"                    => (Tokens.COLON(!line,!line));
<INITIAL>"."                    => (Tokens.DOT(!line,!line));
<INITIAL>"->"                   => (Tokens.RTARROW(!line,!line));
<INITIAL>"<-"                   => (Tokens.LTARROW(!line,!line));
<INITIAL>"=>"                   => (Tokens.DBLARROW(!line,!line));
<INITIAL>"="                    => (Tokens.EQUAL(!line,!line));
<INITIAL>"<>"                   => (Tokens.UNIT(!line,!line));
<INITIAL>"<"                    => (Tokens.LTANGLE(!line,!line));
<INITIAL>">"                    => (Tokens.RTANGLE(!line,!line));
<INITIAL>"("                    => (Tokens.LTPAREN(!line,!line));
<INITIAL>")"                    => (Tokens.RTPAREN(!line,!line));
<INITIAL>"[["                   => (Tokens.LLAM(!line,!line));
<INITIAL>"]]"                   => (Tokens.RLAM(!line,!line));
<INITIAL>"["                    => (Tokens.LTBRACKET(!line,!line));
<INITIAL>"]"                    => (Tokens.RTBRACKET(!line,!line));
<INITIAL>"{"                    => (Tokens.LTBRACE(!line,!line));
<INITIAL>"}"                    => (Tokens.RTBRACE(!line,!line));
<INITIAL>","                    => (Tokens.COMMA(!line,!line));
<INITIAL>"||"                   => (Tokens.PAR(!line,!line));
<INITIAL>"|"                    => (Tokens.BAR(!line,!line));
<INITIAL>"type"                 => (Tokens.TYPE(!line,!line));
<INITIAL>"world"                => (Tokens.WORLD(!line,!line));
<INITIAL>"val"                  => (Tokens.VAL(!line,!line));
<INITIAL>"fun"                  => (Tokens.FUN(!line,!line));
<INITIAL>"case"                 => (Tokens.CASE(!line,!line));
<INITIAL>"of"                   => (Tokens.OF(!line,!line));
<INITIAL>"let"                  => (Tokens.LET(!line,!line));
<INITIAL>"in"                   => (Tokens.IN(!line,!line));
<INITIAL>"end"                  => (Tokens.END(!line,!line));
<INITIAL>"new"                  => (Tokens.NEW(!line,!line));
<INITIAL>"choose"               => (Tokens.CHOOSE(!line,!line));
<INITIAL>"%block"               => (Tokens.BLOCKDEC(!line,!line));
<INITIAL>"some"                 => (Tokens.SOME(yytext,!line,!line));
<INITIAL>"block"                => (Tokens.BLOCK(yytext,!line,!line));
<INITIAL>"create"                => (Tokens.CREATE(!line,!line));
<INITIAL>"all"                  => (Tokens.ALL(!line,!line));
<INITIAL>"all^"                 => (Tokens.ALLOMITTED(!line,!line));
<INITIAL>"exists"               => (Tokens.EXISTS(!line,!line));
<INITIAL>"exists^"              => (Tokens.EXISTSOMITTED(!line,!line));
<INITIAL>"true"                 => (Tokens.TRUE(!line,!line));
<INITIAL>"and"                  => (Tokens.AND(!line,!line));
<INITIAL>"_"                    => (Tokens.UNDERSCORE(!line,!line));
<INITIAL>{uiden}{ws}+"::"       => (Tokens.FORMID(yytext,!line,!line));
<INITIAL>{uiden}                => (Tokens.ID(yytext,!line,!line));
<INITIAL>.                      => (error ("ignoring bad character " ^ yytext,!line, !line); lex());















