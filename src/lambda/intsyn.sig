(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)

signature INTSYN =
sig

  type cid = int			(* Constant identifier        *)
  type name = string			(* Variable name              *)

  (* Contexts *)

  datatype 'a Ctx =			(* Contexts                   *)
    Null				(* G ::= .                    *)
  | Decl of 'a Ctx * 'a			(*     | G, D                 *)
    
  val ctxPop : 'a Ctx -> 'a Ctx
  val ctxLookup: 'a Ctx * int -> 'a
  val ctxLength: 'a Ctx -> int

  datatype Depend =                     (* Dependency information     *)
    No                                  (* P ::= No                   *)
  | Maybe                               (*     | Maybe                *)

  (* Expressions *)

  datatype Uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype Exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (Dec * Depend) * Exp	(*     | Pi (D, P). V         *)
  | Root  of Head * Spine		(*     | H @ S                *)
  | Redex of Exp * Spine		(*     | U @ S                *)
  | Lam   of Dec * Exp			(*     | lam D. U             *)
  | EVar  of Exp option ref * Dec Ctx * Exp * Eqn list
                                        (*     | X<I> : G|-V, Cnstr   *)
  | EClo  of Exp * Sub			(*     | U[s]                 *)

  and Head =				(* Head:                      *)
    BVar  of int			(* H ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Skonst of cid			(*     | c#                   *)
  | Def   of cid			(*     | d                    *)
  | FVar  of name * Exp * Sub		(*     | F[s]                 *)

  and Spine =				(* Spines:                    *)
    Nil					(* S ::= Nil                  *)
  | App   of Exp * Spine		(*     | U ; S                *)
  | SClo  of Spine * Sub		(*     | S[s]                 *)

  and Sub =				(* Explicit substitutions:    *)
    Shift of int			(* s ::= ^n                   *)
  | Dot   of Front * Sub		(*     | Ft.s                 *)

  and Front =				(* Fronts:                    *)
    Idx of int				(* Ft ::= k                   *)
  | Exp of Exp				(*     | U                    *)
  | Undef				(*     | _                    *)

  and Dec =				(* Declarations:              *)
    Dec of name option * Exp		(* D ::= x:V                  *)

  and Eqn =				(* Equations:                 *)
    Eqn of  Dec Ctx * Exp * Exp	       	(* Eqn ::= G|-(U1 == U2)      *)

  (* Type abbreviations *)
  type dctx = Dec Ctx			(* G = . | G,D                *)
  type root = Head * Spine		(* R = H @ S                  *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)

  (* Global signature *)

  exception Error of string		(* raised if out of space     *)
  
  type imp = int			(* # of implicit arguments    *)

  datatype ConDec =			(* Constant declaration       *)
    ConDec of name * imp		(* a : K : kind  or           *)
              * Exp * Uni	        (* c : A : type               *)
  | ConDef of name * imp		(* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | SkoDec of name * imp		(* sa: K : kind  or           *)
              * Exp * Uni	        (* sc: A : type               *)

  val conDecName : ConDec -> name
  val conDecType : ConDec -> Exp

  val sgnAdd   : ConDec -> cid
  val sgnLookup: cid -> ConDec
  val sgnReset : unit -> unit
  val sgnSize  : unit -> int
    
  val constType : cid -> Exp		(* type of c or d             *)
  val constDef  : cid -> Exp		(* definition of d            *)
  val constImp  : cid -> imp
  val constUni  : cid -> Uni

  (* Declaration Contexts *)

  val ctxDec    : dctx * int -> Dec	(* get variable declaration   *)

  (* Explicit substitutions *)

  val id        : Sub			(* id                         *)
  val shift     : Sub			(* ^                          *)
  val invShift  : Sub                   (* ^-1                        *)

  val bvarSub   : int * Sub -> Front    (* k[s]                       *)
  val frontSub  : Front * Sub -> Front	(* H[s]                       *)
  val decSub    : Dec * Sub -> Dec	(* x:V[s]                     *)

  val comp      : Sub * Sub -> Sub	(* s o s'                     *)
  val dot1      : Sub -> Sub		(* 1 . (s o ^)                *)
  val invDot1   : Sub -> Sub		(* (^ o s) o ^-1)             *)

  (* EVar related functions *)

  val newEVar   : dctx * Exp -> Exp	(* creates X:G|-V, []         *) 
  val newEVarCnstr : dctx * Exp * Eqn list -> Exp 
					(* creates X:G|-V, Cnstr      *)
  val newTypeVar : dctx -> Exp		(* creates X:G|-type, []      *)

  (* Type related functions *)

  val targetFamOpt : Exp -> cid option  (* target type family or NONE *)
  val targetFam : Exp -> cid            (* target type family         *)

end;  (* signature INTSYN *)
