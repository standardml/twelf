(* Delphin external syntax *)


signature DEXTSYN = 
sig

(* structure Lexer : LEXER *)

datatype Ast =  Ast of Decs

and Decs 
  = Empty
  | FunDecl of FunDecl * Decs
  | FormDecl of FormDecl * Decs
  | ValDecl of ValDecl * Decs
  | NewDecl of Dec * Decs
  | TwelfDecl of Dec * Decs
  | CreateDecl of CreateDecl * Decs

and CreateDecl
  = Create of Term * CreateDecl
  | Decs of Decs

and FormDecl 
  = Form of string * Form

and FunDecl 
  = Fun of Head * Prog
  | Bar of Head * Prog
  | FunAnd of Head * Prog

and ValDecl
  = Val of Pat * Prog * Form option

and World = 
    WorldIdent of string
  | Plus of World * World
  | Concat of World * World
  | Times of World

and Form 
  = True
  | Forall of Dec * Form
  | ForallOmitted of Dec * Form
  | Exists of Dec * Form
  | ExistsOmitted of Dec * Form
  | And of Form * Form
  | World of World * Form
(* | Arrow of Form * Form *)
(* | WldDef of (string list) * Form *)

and Prog 
  = Unit 
  | Pair of Prog * Prog
  | AppProg of Prog * Prog
  | AppTerm of Prog * Term
  | Inx of Term * Prog 
  | Lam of Dec * Prog
  | Const of string
  | Case of  (Pat list * Prog) list
  | Let of Decs * Prog 
  | Par of Prog * Prog
  | New of Dec list * Prog 
  | Choose of Dec * Prog 
(* | Rec of MDec * Prog *)

and Cases 
  = First of Pat * Prog
  | Alt of Cases * Pat * Prog

and Head 
  = Head of string
  | AppLF of Head * Term
  | AppMeta of Head * Pat

and Pat 
  = PatInx of Term * Pat
  | PatPair of Pat * Pat
  | PatVar of MDec
  | PatUnderscore 
  | PatUnit 

and MDec 
  = MDec of string * (Form option)

and Block 
  = Block of string list

(* and Term 
  = Term of string
*)
and Term 
  = Rtarrow of Term * Term
  | Ltarrow of Term * Term
  | Type
  | Id of string
  | Pi of Dec * Term
  | Fn of Dec * Term
  | App of Term * Term
  | Dot of Term * string
  | Paren of Term
  | Omit
  | Of of Term * Term

and Dec 
  = Dec of string * Term
end







