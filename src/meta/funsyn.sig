(* Internal syntax for functional proof term calculus *)
(* Author: Carsten Schuermann *)

signature FUNSYN = 
sig
  (*! structure IntSyn : INTSYN !*)

  (* make abstract *)
  type label = int      
  type lemma = int 

  datatype LabelDec =			(* ContextBody                *)
    LabelDec of string * IntSyn.Dec list * IntSyn.Dec list
					(* BB ::= l: SOME Theta. Phi  *)

  datatype CtxBlock =                   (* ContextBlocks              *)
    CtxBlock of 
     label option * IntSyn.dctx		(* B ::= l : Phi              *) 

  datatype LFDec =			(* Contexts                   *)
    Prim of IntSyn.Dec			(* LD ::= x :: A              *)
  | Block of CtxBlock			(*      | B                   *)

  (* ??? *)
  type lfctx = LFDec IntSyn.Ctx         (* Psi ::= . | Psi, LD        *) 

  datatype For =			(* Formulas                   *)
    All of LFDec * For			(* F ::= All LD. F            *)
  | Ex  of IntSyn.Dec * For		(*     | Ex  D. F             *)
  | True				(*     | T                    *)
  | And of For * For                    (*     | F1 ^ F2              *)

  datatype Pro =			(* Programs                   *)
    Lam of LFDec * Pro			(* P ::= lam LD. P            *)
  | Inx of IntSyn.Exp * Pro             (*     | <M, P>               *)
  | Unit				(*     | <>                   *)
  | Rec of MDec * Pro			(*     | mu xx. P             *)
  | Let of Decs * Pro			(*     | let Ds in P          *)
  | Case of Opts                        (*     | case O               *)
  | Pair of Pro * Pro                   (*     | <P1, P2>             *)

  and Opts =				(* Option list                *)
    Opts of (lfctx * IntSyn.Sub * Pro) list
                                        (* O ::= (Psi' |> s |-> P     *)

  and MDec =				(* Meta Declaration:          *)
    MDec of string option * For		(* DD ::= xx : F              *)
 
  and Decs =				(* Declarations               *)
    Empty				(* Ds ::= .                   *)
  | Split of int * Decs			(*      | <x, yy> = P, Ds     *)
  | New of CtxBlock * Decs		(*      | nu B. Ds            *)
  | App of (int * IntSyn.Exp) * Decs	(*      | xx = yy M, Ds       *)
  | PApp of (int * int) * Decs		(*      | xx = yy Phi, Ds     *)
  | Lemma of lemma * Decs               (*      | xx = cc, Ds         *)
  | Left of int * Decs                  (*      | xx = pi1 yy, Ds     *)
  | Right of int * Decs                 (*      | xx = pi2 yy, Ds     *)
 
  datatype LemmaDec =			(* Lemmas                     *)
    LemmaDec of string list * Pro * For	(* L ::= c:F = P              *)

  (* ??? *)
  type mctx = MDec IntSyn.Ctx           (* Delta ::= . | Delta, xx : F*)

  val labelLookup : label -> LabelDec
  val labelAdd : LabelDec -> label
  val labelSize : unit -> int
  val labelReset : unit -> unit

  val lemmaLookup : lemma -> LemmaDec
  val lemmaAdd : LemmaDec -> lemma
  val lemmaSize : unit -> int

  val mdecSub : MDec * IntSyn.Sub -> MDec
  val makectx : lfctx -> IntSyn.dctx

  val lfctxLength : lfctx -> int
  val lfctxLFDec : (lfctx * int) -> (LFDec * IntSyn.Sub) 


  val dot1n : (IntSyn.dctx * IntSyn.Sub) -> IntSyn.Sub

  val convFor : (For * IntSyn.Sub) * 
                (For * IntSyn.Sub) -> bool
  val forSub : For * IntSyn.Sub -> For
  val normalizeFor : For * IntSyn.Sub -> For

  val listToCtx : IntSyn.Dec list -> IntSyn.dctx
  val ctxToList : IntSyn.dctx -> IntSyn.Dec list
end (* Signature FUNSYN *)       






