module TwelfLex (runitall) where

import Control.Monad
import Char

newtype Parser a = Parser (String -> [(a,String)])

-- Parsing primitives ------------------------------------------------

parse :: Parser a -> String -> [(a,String)]
parse (Parser p) = p

item :: Parser Char
item = Parser (\cs -> case cs of 
			""	-> []
			(c:cs)  -> [(c,cs)])

sat :: (Char -> Bool) -> Parser Char
sat p = do {c <- item; if p c then return c else mzero}

-- Monad of parsers: -------------------------------------------------

instance Monad Parser where
   return a      = Parser (\cs -> [(a,cs)])
   p >>= f       = Parser (\cs -> concat [parse (f a) cs' |
                                     (a,cs') <- parse p cs])

instance MonadPlus Parser where
   mzero          = Parser (\cs -> [])
   mplus p q      = Parser (\cs -> mplus (parse p cs) (parse q cs))

-- Efficiency imporving combinators: ---------------------------------

force :: Parser a -> Parser a
force p = Parser (\cs -> let xs = parse p cs in xs)
--			(fst (head xs), snd (head xs)))

(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser (\cs -> case parse (mplus p q) cs of 
				[]     -> []
				(x:xs) -> [x])

-- Lexical combinators: ----------------------------------------------

space           :: Parser String
space            = many (sat isSpace)

space1          :: Parser String
space1           = many1 (sat isSpace)

token           :: Parser a -> Parser a
token p          = do {a <- p; space; return a}

apply           :: Parser a -> String -> [(a,String)]
apply p          = parse (do {space; p})

-- Useful parsers: ---------------------------------------------------

char            :: Char -> Parser Char
char c           = sat (c ==)

digit           :: Parser Int
digit            = do {c <- sat isDigit; return (ord c - ord '0')}

lower           :: Parser Char
lower            = sat isLower

upper           :: Parser Char
upper            = sat isUpper

letter          :: Parser Char
letter           = sat isAlpha

alphanum        :: Parser Char
alphanum         = sat isAlphaNum

-- symb            :: String -> Parser String
-- symb cs          = token (string cs)

ident           :: [String] -> Parser String
ident css        = do cs <- token identifier
                      guard (not (elem cs css))
                      return cs

identifier      :: Parser String
identifier       = do {c <- lower; cs <- many alphanum; return (c:cs)}

nat             :: Parser Int
nat              = token natural

natural         :: Parser Int
natural          = digit `chainl1` return (\m n -> 10*m + n)

int             :: Parser Int
int              = token integer

integer         :: Parser Int
integer          = do {char '-'; n <- natural; return (-n)} +++ nat


-- Recursion combinators: --------------------------------------------

string          :: String -> Parser String
string ""        = return ""
string (c:cs)    = do {char c; string cs; return (c:cs)}

many            :: Parser a -> Parser [a]
many p           = force (many1 p +++ return [])

many1           :: Parser a -> Parser [a]
many1 p          = do {a <- p; as <- many p; return (a:as)}

sepby           :: Parser a -> Parser b -> Parser [a]
p `sepby` sep    = (p `sepby1` sep) +++ return []

sepby1          :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep   = do {a <- p; as <- many (do {sep; p}); return (a:as)}

chainl          :: Parser a -> Parser (a -> a -> a) -> a -> Parser a
chainl p op a    = (p `chainl1` op) +++ return a

chainl1         :: Parser a -> Parser (a -> a -> a) -> Parser a
p `chainl1` op   = do {a <- p; rest a}
                   where
                      rest a = do {f <- op; b <- p; rest (f a b)}
                               +++ return a

-- comment :: String -> Parser String
-- seekend :: String -> Parser String
-- commentleaf :: String -> Parser String

commentnormal :: Parser String
commentnormal = do a <- sat (\c -> not (or [c == '%',c == '}']))
		   return [a]

commentnotstart:: Parser String
commentnotstart = do char '%'
	             a <- sat (\c -> not ('{' == c))
	             return (['%',a])

commentnotend  :: Parser String
commentnotend   = do char '}'
		     a <- sat (\c -> not ('%' == c))
		     return (['}',a])

linecomment    :: Parser String
linecomment     = do char '%'
                     a <- mplus (char '%') (sat isSpace) 
                     b <- many (sat (\c -> not (c == '\n')))
		     return ([a] ++ b)

comment        :: Parser String
comment 	= do a <- string "%{"
	     	     b <- many (mplus commentnormal 
                               (mplus commentnotstart
                       	       (mplus commentnotend comment)))
                     c <- string "}%"
                     return (a ++ (concat b) ++ c)

quote :: Parser String
quote = do a <- string "\""
           b <- many (sat (\c -> not (c == '\"')))
           c <- string "\""
           return (a ++ b ++ c)

idMember :: Char -> Bool
idMember c = not (or [c == ':',c == '.', c == '(', c == ')',
		      c == '[',c == ']', c == '{', c == '}',
		      c == '%',c == '"', isSpace c])

upID :: Parser String
upID = do a <- upper
          b <- many (sat idMember)
          return (a : b)

downID :: Parser String
downID = do a <- sat (\c -> and [idMember c,not (isUpper c)])
            b <- many (sat idMember)
            return ([a] ++ b)

data Lex = Tok String String 
         | UpID String String 
         | DownID String String
         | Decl String String
         | Comment String String
         | LineCom String String
         | Quote String String
         | ArrL String
         | ArrR String
         | Eq String
         | Colon String
         | ParenL String
         | ParenR String
         | BrackL String
         | BrackR String
         | CurlyL String
         | CurlyR String
         | Type String
         | Period String

showsLex :: Lex -> String -> String
showsLex (Tok t _)    = \s -> "Tok(" ++ t ++ (')' : s)
showsLex (UpID t _)   = \s -> "UpID(" ++ t ++ (')' : s)
showsLex (DownID t _) = \s -> "DownID(" ++ t ++ (')' : s)
showsLex (Decl t _)   = \s -> "Decl(" ++ t ++ (')' : s)
showsLex (Comment t _)= \s -> "Comment(" ++ t ++ (')' : s)
showsLex (LineCom t _)= \s -> "LineCom(" ++ t ++ (')' : s)
showsLex (Quote t _)  = \s -> "Quote(" ++ t ++ (')' : s)
showsLex (Type _)     = ("Type" ++)
showsLex (ArrL _)     = ("ArrL" ++)
showsLex (ArrR _)     = ("ArrR" ++)
showsLex (Eq _)       = ("Eq" ++)
showsLex (Colon _)    = ("Colon" ++)
showsLex (ParenL _)   = ("ParenL" ++)
showsLex (ParenR _)   = ("ParenR" ++)
showsLex (BrackL _)   = ("BrackL" ++)
showsLex (BrackR _)   = ("BrackR" ++)
showsLex (CurlyL _)   = ("CurlyL" ++)
showsLex (CurlyR _)   = ("CurlyR" ++)
showsLex (Period _)   = ("Period" ++)


outputLex :: Lex -> String
outputLex (UpID t w)   = 
                  "<span style=\"color: #000099;\">" ++
                  t ++ "</span>" ++ w
outputLex (DownID t w) = t ++ w
outputLex (Decl t w)   = 
                  "<span style=\"color: #6633FF;\">" ++
                  t ++ "</span>" ++ w
outputLex (Comment t w)= 
                  "<span style=\"font-weight: bold; color: #444444;\">" ++
                  t ++ "</span>" ++ w
outputLex (LineCom t w)= 
                  "<span style=\"font-weight: bold; color: #444444;\">" ++
                  t ++ "</span>" ++ w
outputLex (Quote t w)  = t ++ w
outputLex (Type w)     = (("type" ++ w))
outputLex (ArrL w)     = (("<-" ++ w))
outputLex (ArrR w)     = (("->" ++ w))
outputLex (Eq w)       = (('=' : w))
outputLex (Colon w)    = ((':' : w))
outputLex (ParenL w)   = (('(' : w))
outputLex (ParenR w)   = ((')' : w))
outputLex (BrackL w)   = (('[' : w))
outputLex (BrackR w)   = ((')' : w))
outputLex (CurlyL w)   = (('{' : w))
outputLex (CurlyR w)   = (('}' : w))
outputLex (Period w)   = (('.' : w))



instance Show Lex where
    showsPrec _ x = showsLex x



aLex :: Parser Lex
aLex = (do {a <- comment; b <- space; return (Comment a b)}) +++
       (do {a <- linecomment; b <- space; return (LineCom a b)}) +++
--- Keywords ----------------------------------------------------------
       (do {a <- string "type"; b <- space; return (Type b)}) +++
       (do {a <- string "<-"; b <- space; return (ArrL b)}) +++
       (do {a <- string "->"; b <- space; return (ArrR b)}) +++
--- Special Characters ------------------------------------------------
       (do {a <- char '='; b <- space; return (Eq b)}) +++
       (do {a <- char ':'; b <- space; return (Colon b)}) +++
       (do {a <- char '('; b <- space; return (ParenL b)}) +++
       (do {a <- char ')'; b <- space; return (ParenR b)}) +++
       (do {a <- char '['; b <- space; return (BrackL b)}) +++
       (do {a <- char ']'; b <- space; return (BrackR b)}) +++
       (do {a <- char '{'; b <- space; return (CurlyL b)}) +++
       (do {a <- char '}'; b <- space; return (CurlyR b)}) +++
       (do {a <- quote; b <- space; return (Quote a b)}) +++
--- Identifiers and declarations --------------------------------------
       (do {a <- upID; b <- space; return (UpID a b)}) +++
       (do {a <- downID; b <- space; return (DownID a b)}) +++
       (do {char '%'; b <- many1 lower; c <- space; return (Decl b c)})

            

lexDecl :: Parser [Lex]
lexDecl = do a <- many aLex
             b <- (do {a <- char '.'; b <- space; return (Period b)})
             return (a ++ [b])

lexSig :: Parser (String,[[Lex]])
lexSig = do a <- space
            b <- many lexDecl
            c <- many aLex
            d <- many (sat (\c -> True))
            return (a,b ++ [c] ++ [[Comment d ""]])

doLex :: String -> [[Lex]]
doLex s = snd (fst (head (parse lexSig s)))

outputDecl :: [Lex] -> String
outputDecl list = concat [outputLex x |x <- list]

outputDecl1 :: [Lex] -> String
outputDecl1 ((DownID t w):ls) = 
		 "<span style=\"color: #990000;\">" ++ t ++ "</span>" ++ w
  		 ++ outputDecl ls
outputDecl1 (l:ls) = outputLex l ++ outputDecl1 ls
outputDecl1 nil = ""

outputSig :: [[Lex]] -> String
outputSig s = concat [outputDecl1 x | x <- s]

runitall :: String -> String
runitall s = outputSig (doLex s)

