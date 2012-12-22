" Vim syntax file
" Language:        Twelf
" Last Change:     January 19, 2012
"
" Version:         1.0
" Original Author: unknown
"
" Modifications:   Ryan Pearl <rpearl@andrew.cmu.edu>

" Remove any old syntax stuff hanging around
if version < 600
  syntax clear
elseif exists("b:current_syntax")
  finish
endif

" Just about anything in Twelf is a keyword character
set iskeyword+=@,!,#-',*-45,47-57,59-90,94-122,\|,^:

" We'll define some color schemes up here--the actual tokens use these `Face'
" definitions
hi def link twelfDeclarationFace  Identifier
hi def link twelfPercentKeyFace   Keyword
hi def link twelfTypeFace         Constant
hi def link twelfCommentFace      Comment
hi def link twelfSymbolFace       Macro
hi def link twelfPunctuationFace  Special
hi def link twelfFreeVariableFace Number
hi def link twelfCurlyFace        Delimiter
hi def link twelfSquareFace       Delimiter


syn keyword twelfPercentKey %mode %infix %prefix %abbrev %postfix %name %freeze %clause %define %solve %querytabled %query %tabled %deterministic %unique %block %worlds %covers %total %terminates %reduces %theorem %prove %assert %establish %sig %struct %where %include %open %use

syn keyword twelfType type
syn match twelfPunct ":\|\.\|\<=\>"
syn match twelfFVar "\<[A-Z_]\k*\>"
syn keyword twelfSymbol -> <-
syn match twelfDecl "^\s*[^A-Z_]\k*\s*:" contains=twelfPunct


syn match twelfCurly "{\|}" contained
syn match twelfSquare "\[\|\]" contained
syn match twelfBindDecl "[^A-Z_{\[]\k*\s*:" contains=twelfPunct contained
syn region twelfPiBind start="{" end="}" keepend transparent contains=twelfCurly,twelfPunct,twelfFVar,twelfSymbol,twelfType,twelfBindDecl
syn region twelfLamBind start="\[" end="\]" keepend transparent contains=twelfSquare,twelfPunct,twelfFVar,twelfSymbol,twelfType,twelfBindDecl

"syn region twelfCommand start="^" end="\." keepend transparent contains=ALL

syn match twelfParen "(\|)" contained
syn region twelfParens start="(" end=")" transparent contains=ALL


" Comments hilighting 
"  single line, empty line comments
syn match twelfComment  "% .*\|%%.*\|%$"
"  delimited comments, needs to contain itself to properly hilight nested
"  comments 
syn region twelfDelimitedComment  start="%{" end="}%" contains=twelfDelimitedComment 

" Assign coloration
hi link twelfType              twelfTypeFace
hi link twelfPercentKey        twelfPercentKeyFace
hi link twelfComment           twelfCommentFace
hi link twelfDelimitedComment  twelfCommentFace
hi link twelfSymbol            twelfSymbolFace
hi link twelfPunct             twelfPunctuationFace
hi link twelfParen             twelfSymbolFace
hi link twelfDecl              twelfDeclarationFace
hi link twelfBindDecl          twelfDeclarationFace
hi link twelfFVar              twelfFreeVariableFace
hi link twelfCurly             twelfCurlyFace
hi link twelfSquare            twelfSquareFace

" Indentation

" Folds
"syn region myFold start="%{" end="}%" transparent fold 
"syn sync fromstart
"set foldmethod=syntax
"set foldminlines=3

" Set the current syntax name
let b:current_syntax = "twelf"
