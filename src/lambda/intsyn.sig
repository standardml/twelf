(* Internal Syntax *)
(* Author: Frank Pfenning, Carsten Schuermann *)
(* Modified: Roberto Virga *)

signature INTSYN =
sig

  type cid = int			(* Constant identifier        *)
  type mid = int                        (* Structure identifier       *)
  type csid = int                       (* CS module identifier       *)
 
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
  | Meta				(*     | Meta                 *)

  (* expressions *)

  datatype Uni =			(* Universes:                 *)
    Kind				(* L ::= Kind                 *)
  | Type				(*     | Type                 *)

  datatype Exp =			(* Expressions:               *)
    Uni   of Uni			(* U ::= L                    *)
  | Pi    of (Dec * Depend) * Exp	(*     | Pi (D, P). V         *)
  | Root  of Head * Spine		(*     | H @ S                *)
  | Redex of Exp * Spine		(*     | U @ S                *)
  | Lam   of Dec * Exp			(*     | lam D. U             *)
  | EVar  of Exp option ref * Dec Ctx * Exp * (Cnstr ref) list ref
                                        (*     | X<I> : G|-V, Cnstr   *)
  | EClo  of Exp * Sub			(*     | U[s]                 *)
  | FgnExp of csid *                    (*     | (foreign expression) *)
      {
        toInternal : unit -> Exp,       (* convert to internal syntax *)
        map : (Exp -> Exp) -> Exp,      (* apply to subterms          *)
        equalTo : Exp -> bool,
                                        (* test for equality          *)
        unifyWith : Dec Ctx * Exp -> FgnUnify
                                        (* unify with another term    *)
      }

  and Head =				(* Head:                      *)
    BVar  of int			(* H ::= k                    *)
  | Const of cid			(*     | c                    *)
  | Proj  of Block * int		(*     | #k(b)                *)
  | Skonst of cid			(*     | c#                   *)
  | Def   of cid			(*     | d (strict)           *)
  | NSDef of cid			(*     | d (non strict)       *)
  | FVar  of string * Exp * Sub		(*     | F[s]                 *)
  | FgnConst of csid * ConDec           (*     | (foreign constant)   *)

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
  | Block of Block			(*     | _x                   *)
  | Undef				(*     | _                    *)

  and Dec =				(* Declarations:              *)
    Dec of string option * Exp		(* D ::= x:V                  *)
  | BDec of cid * Sub			(*     | v:l[s]               *)

  and Block =				(* Blocks:                    *)
    Bidx of int				(* b ::= v                    *)
  | LVar of Block option ref * cid * Sub 
                                        (*     | L(l,s)               *)
  | BClo of Block * Sub                 (*     | b[s]                 *)

  (* constraints *)

  and Cnstr =				(* Constraint:                *)
    Solved                      	(* Cnstr ::= solved           *)
  | Eqn      of Dec Ctx * Exp * Exp     (*         | G|-(U1 == U2)    *)
  | FgnCnstr of csid *                  (*         | (foreign)        *)
      {
        toInternal : unit -> (Dec Ctx * Exp) list,
                                        (* convert to internal syntax *)
        awake : unit -> bool,           (* awake                      *)
        simplify : unit -> bool         (* simplify                   *)
      }

  and Status =                          (* Status of a constant:      *)
    Normal                              (*   inert                    *)
  | Constraint of csid * (Dec Ctx * Spine * int -> Exp option)
                                        (*   acts as constraint       *)
  | Foreign of csid * (Spine -> Exp)    (*   is converted to foreign  *)

  and FgnUnify =                        (* Result of foreign unify    *)
    Succeed of FgnUnifyResidual list
    (* succeed with a list of residual operations *)
  | Fail

  and FgnUnifyResidual =
    Assign of Dec Ctx * Exp * Exp * Sub
    (* perform the assignment G |- X = U [ss] *)
  | Delay of Exp * Cnstr ref
    (* delay cnstr, associating it with all the rigid EVars in U  *)

  (* Global signature *)

  and ConDec =			        (* Constant declaration       *)
    ConDec of string * mid option * int * Status
                                        (* a : K : kind  or           *)
              * Exp * Uni	        (* c : A : type               *)
  | ConDef of string * mid option * int	(* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | AbbrevDef of string * mid option * int
                                        (* a = A : K : kind  or       *)
              * Exp * Exp * Uni		(* d = M : A : type           *)
  | BlockDec of string * mid option     (* %block l : SOME G1 PI G2   *)
              * Dec Ctx * Dec list
  | SkoDec of string * mid option * int	(* sa: K : kind  or           *)
              * Exp * Uni	        (* sc: A : type               *)

  datatype StrDec =                     (* Structure declaration      *)
      StrDec of string * mid option

  (* Type abbreviations *)
  type dctx = Dec Ctx			(* G = . | G,D                *)
  type eclo = Exp * Sub   		(* Us = U[s]                  *)
  type bclo = Block * Sub   		(* Bs = B[s]                  *)
  type cnstr = Cnstr ref

  exception Error of string		(* raised if out of space     *)
  
  val conDecName   : ConDec -> string
  val conDecParent : ConDec -> mid option
  val conDecImp    : ConDec -> int
  val conDecStatus : ConDec -> Status
  val conDecType   : ConDec -> Exp
  val conDecBlock  : ConDec -> dctx * Dec list   

  val strDecName   : StrDec -> string
  val strDecParent : StrDec -> mid option

  val sgnReset     : unit -> unit
  val sgnSize      : unit -> cid * mid

  val sgnAdd   : ConDec -> cid
  val sgnLookup: cid -> ConDec
  val sgnApp   : (cid -> unit) -> unit

  val sgnStructAdd    : StrDec -> mid
  val sgnStructLookup : mid -> StrDec

  val constType   : cid -> Exp		(* type of c or d             *)
  val constDef    : cid -> Exp		(* definition of d            *)
  val constImp    : cid -> int
  val constStatus : cid -> Status
  val constUni    : cid -> Uni

  (* Declaration Contexts *)

  val ctxDec    : dctx * int -> Dec	(* get variable declaration   *)
  val blockDec  : dctx * Block * int -> Dec 

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

  val newEVar    : dctx * Exp -> Exp	(* creates X:G|-V, []         *) 
  val newTypeVar : dctx -> Exp		(* creates X:G|-type, []      *)

  (* Type related functions *)

  val targetFamOpt : Exp -> cid option  (* target type family or NONE *)
  val targetFam : Exp -> cid            (* target type family         *)

end;  (* signature INTSYN *)
