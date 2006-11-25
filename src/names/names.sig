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

  (* Constant names and fixities *)

  datatype Qid = Qid of string list * string

  val qidToString : Qid -> string
  val stringToQid : string -> Qid option
  val unqualified : Qid -> string option

  type namespace

  val newNamespace : unit -> namespace
  val insertConst : namespace * IntSyn.cid -> unit (* shadowing disallowed *)
  val insertStruct : namespace * IntSyn.mid -> unit (* shadowing disallowed *)
  val appConsts : (string * IntSyn.cid -> unit) -> namespace -> unit
  val appStructs : (string * IntSyn.mid -> unit) -> namespace -> unit

  val reset : unit -> unit
  val resetFrom : IntSyn.cid * IntSyn.mid -> unit

  (* The following functions have to do with the mapping from names
     to cids/mids only. *)
  val installConstName : IntSyn.cid -> unit
  val installStructName : IntSyn.mid -> unit

  val constLookup : Qid -> IntSyn.cid option
  val structLookup : Qid -> IntSyn.mid option
  val constUndef : Qid -> Qid option (* shortest undefined prefix of Qid *)
  val structUndef : Qid -> Qid option

  val constLookupIn : namespace * Qid -> IntSyn.cid option
  val structLookupIn : namespace * Qid -> IntSyn.mid option
  val constUndefIn : namespace * Qid -> Qid option
  val structUndefIn : namespace * Qid -> Qid option

  (* This function maps cids/mids to names.  It uses the information in
     the IntSyn.ConDec or IntSyn.StrDec entries only, and only considers
     the name->cid/mid mapping defined above in order to tell whether a
     name is shadowed (any constant or structure whose canonical name
     would map to something else, or to nothing at all, in the case of
     an anonymous structure, is shadowed). *)
  val conDecQid : IntSyn.ConDec -> Qid
  val constQid : IntSyn.cid -> Qid (* will mark if shadowed *)
  val structQid : IntSyn.mid -> Qid (* will mark if shadowed *)

  val installFixity : IntSyn.cid * Fixity.fixity -> unit
  val getFixity : IntSyn.cid -> Fixity.fixity
  val fixityLookup : Qid -> Fixity.fixity (* Nonfix if undefined *)

  (* Name preferences for anonymous variables: a, EPref, UPref *)
  val installNamePref : IntSyn.cid * (string list * string list) -> unit
  val getNamePref : IntSyn.cid -> (string list * string list) option

  val installComponents : IntSyn.mid * namespace -> unit
  val getComponents : IntSyn.mid -> namespace

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
