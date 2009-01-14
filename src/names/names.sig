(* Names of Constants and Variables *)
(* Author: Frank Pfenning *)
(* Modified: Jeff Polakow *)

signature FIXITY =
sig

  datatype associativity = Left | Right | None
  datatype precedence = Strength of int

  val maxPrec : precedence
  val minPrec : precedence

  val less : precedence * precedence -> bool
  val leq : precedence * precedence -> bool
  val compare : precedence * precedence -> order

  val inc : precedence -> precedence
  val dec : precedence -> precedence

  datatype fixity =
      Nonfix
    | Infix of precedence * associativity
    | Prefix of precedence
    | Postfix of precedence

  val prec : fixity -> precedence
  val toString : fixity -> string

  (* returns integer for precedence such that lower values correspond to higher precedence, useful for exports *)
  val precToIntAsc : fixity -> int
  
end;  (* signature FIXITY *)

signature NAMES =
sig
  (*! structure IntSyn : INTSYN !*)

  exception Error of string
  exception Unprintable

  structure Fixity : FIXITY

  (* maps global declaration id's to their local qualified names *)
  val installName : IDs.cid * string list -> unit
  val nameLookup : IDs.mid * string list -> IDs.cid option

  (* maps global declaration id's to their fixities, Nonfix if undefined *)
  val installFixity : IDs.cid * Fixity.fixity -> unit
  val fixityLookup : IDs.cid -> Fixity.fixity

  (* maps global declaration id's to their name preferences *)
  val installNamePref : IDs.cid * (string list * string list) -> unit
  val namePrefLookup : IDs.cid -> (string list * string list) option

val parseQualifiedName : string -> string list (* temporary *)
  (* resets the above three mappings *)
  val reset : unit -> unit

  (* EVar and BVar name choices *)
  val varReset : IntSyn.dctx -> unit (* context in which EVars are created *)
  val addEVar : IntSyn.Exp * string -> unit (* assumes name not already used *)
  val getEVarOpt : string -> IntSyn.Exp option (* NONE, if undefined or not EVar *)
  val evarName : IntSyn.dctx * IntSyn.Exp -> string (* create, if undefined *)
  val bvarName : IntSyn.dctx * int -> string (* raises Unprintable if undefined *)

  val decName  : IntSyn.dctx * IntSyn.Dec -> IntSyn.Dec (* status unknown, like decEName *)
  val decEName : IntSyn.dctx * IntSyn.Dec -> IntSyn.Dec (* assign existential name *)
  val decUName : IntSyn.dctx * IntSyn.Dec -> IntSyn.Dec (* assign universal name *)
  val decLUName: IntSyn.dctx * IntSyn.Dec -> IntSyn.Dec (* assign local universal name *)

  val ctxName  : IntSyn.dctx -> IntSyn.dctx (* assign global existential names *)
  val ctxLUName: IntSyn.dctx -> IntSyn.dctx (* assign local universal names *)

  val nameConDec : IntSyn.ConDec -> IntSyn.ConDec

  (* Skolem constants *)
  val skonstName : string -> string

  (* Named EVars, used for queries *)
  val namedEVars : unit -> (IntSyn.Exp * string) list
  (* Uninstantiated named EVars with constraints *)
  val evarCnstr : unit -> (IntSyn.Exp * string) list
end;  (* signature NAMES *)
