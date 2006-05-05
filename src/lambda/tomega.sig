(* Internal syntax for Delphin *)
(* Author: Carsten Schuermann *)

signature TOMEGA = 
sig
  (*! structure IntSyn : INTSYN !*)

  (* make abstract *)
  type label = int      
  type lemma = int 

  datatype Worlds = Worlds of IntSyn.cid list
    
  datatype Quantifier = Implicit | Explicit


  datatype TC	=			(* Terminiation Condition     *)
    Abs of IntSyn.Dec * TC      	(* T ::= {{D}} O              *)
  | Conj of TC * TC			(*     | O1 ^ O2              *)
  | Base of ((IntSyn.Exp * IntSyn.Sub) * 
	     (IntSyn.Exp * IntSyn.Sub)) Order.Order

  datatype For  			(* Formulas                   *)
  = World of Worlds * For               (* F ::= World l1...ln. F     *)  
  | All of (Dec * Quantifier) * For     (*     | All LD. F            *)
  | Ex  of (IntSyn.Dec * Quantifier)  * For
					(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of For * For                    (*     | F1 ^ F2              *)
  | FClo of For * Sub			(*     | F [t]                *)
  | FVar of (Dec IntSyn.Ctx * For option ref)
					(*     | F (G)                *)

  and Dec =			        (* Declaration:               *)
    UDec of IntSyn.Dec                  (* D ::= x:A                  *)
  | PDec of string option * For * TC option * TC option  
                                        (*     | xx :: F              *)

  and Prg =				(* Programs:                  *)
    Box of Worlds * Prg                 (*     | box W. P             *)
  | Lam of Dec * Prg	 	        (*     | lam LD. P            *)
  | New of Prg                          (*     | new P                *)
  | Choose of Prg                       (*     | choose P             *)
  | PairExp of IntSyn.Exp * Prg         (*     | <M, P>               *)
  | PairBlock of IntSyn.Block * Prg     (*     | <rho, P>             *) 
  | PairPrg of Prg * Prg                (*     | <P1, P2>             *)
  | Unit				(*     | <>                   *)
  | Redex of Prg * Spine
  | Rec of Dec * Prg			(*     | mu xx. P             *)
  | Case of Cases                       (*     | case t of O          *)
  | PClo of Prg * Sub			(*     | P [t]                *)
  | Let of Dec * Prg * Prg              (*     | let D = P1 in P2     *)
  | EVar of Dec IntSyn.Ctx * Prg option ref * For * TC option * TC option * IntSyn.Exp
					(*     | E (G, F, _, _, X)    *)
                                        (* X is just just for printing*)
    
  | Const of lemma                      (* P ::= cc                   *)
  | Var of int                          (*     | xx                   *)
  | LetPairExp of IntSyn.Dec * Dec * Prg * Prg
  | LetUnit of Prg * Prg

  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | AppExp of IntSyn.Exp * Spine        (*     | P U                  *) 
  | AppBlock of IntSyn.Block * Spine    (*     | P rho                *)
  | AppPrg of Prg * Spine               (*     | P1 P2                *)
  | SClo of Spine * Sub                 (*     | S [t]                *) 
 
  and Sub =				(* Substitutions:             *)
    Shift of int			(* t ::= ^n                   *)
  | Dot of Front * Sub			(*     | F . t                *)
      
  and Front =				(* Fronts:                    *)
    Idx of int		  	        (* F ::= i                    *)
  | Prg of Prg				(*     | p                    *)
  | Exp of IntSyn.Exp			(*     | U                    *)
  | Block of IntSyn.Block		(*     | _x                   *)
  | Undef                               (*     | _                    *)

  and Cases =				(* Cases                      *)
    Cases of (Dec IntSyn.Ctx * Sub * Prg) list
					(* C ::= (Psi' |> s |-> P)    *)

  datatype ConDec =			(* ConDec                     *)
    ForDec of string * For		(* CD ::= f :: F              *)
  | ValDec of string * Prg * For	(*      | f == P              *)

  exception NoMatch
  val coerceSub : Sub -> IntSyn.Sub
  val embedSub  : IntSyn.Sub -> Sub
  val coerceCtx : Dec IntSyn.Ctx -> IntSyn.Dec IntSyn.Ctx
  val strengthenCtx : Dec IntSyn.Ctx -> (IntSyn.Dec IntSyn.Ctx * Sub * Sub)
  val embedCtx  : IntSyn.Dec IntSyn.Ctx -> Dec IntSyn.Ctx
  val weakenSub : Dec IntSyn.Ctx -> Sub
  val invertSub : Sub -> Sub
  val id        : Sub
  val shift     : Sub
  val dot1      : Sub -> Sub
  val dotEta    : Front * Sub -> Sub
  val comp      : Sub * Sub -> Sub
  val varSub    : int * Sub -> Front
  val decSub    : Dec * Sub -> Dec
  val forSub    : For * Sub -> For
  val whnfFor   : For * Sub -> For * Sub
  val normalizePrg : Prg * Sub -> Prg 
  val normalizeSub : Sub -> Sub 
  val derefPrg : Prg -> Prg 
  
  val lemmaLookup : lemma -> ConDec
  val lemmaName   : string -> lemma
  val lemmaAdd    : ConDec -> lemma
  val lemmaSize   : unit -> int
  val lemmaDef    : lemma -> Prg
  val lemmaFor    : lemma -> For

  val eqWorlds    : Worlds * Worlds -> bool

  val convFor     : (For * Sub) * (For * Sub) -> bool
  val newEVar     : Dec IntSyn.Ctx * For -> Prg
  val newEVarTC   : Dec IntSyn.Ctx * For * TC option * TC option -> Prg 

(* Below are added by Yu Liao *)
  val ctxDec : Dec IntSyn.Ctx * int -> Dec
  val revCoerceSub : IntSyn.Sub -> Sub
  val revCoerceCtx : IntSyn.Dec IntSyn.Ctx -> Dec IntSyn.Ctx

(* Added references by ABP *)
  val coerceFront : Front -> IntSyn.Front
  val revCoerceFront : IntSyn.Front -> Front
  val deblockify : IntSyn.Dec IntSyn.Ctx -> IntSyn.Dec IntSyn.Ctx * Sub

(* Stuff that has to do with termination conditions *)
  val TCSub : TC * IntSyn.Sub -> TC
  val normalizeTC : TC -> TC
  val convTC : TC * TC -> bool
  val transformTC : IntSyn.Dec IntSyn.Ctx * For * int Order.Order list -> TC
    

end (* Signature TOMEGA *)




