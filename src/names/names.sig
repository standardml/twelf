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
  
end;  (* signature FIXITY *)

signature NAMES =
sig
  (*! structure IntSyn : INTSYN !*)

  exception Error of string
  exception Unprintable

  structure Fixity : FIXITY

  (* map between global declarations ids (IDs.cid) and their local qualified names (string list)
     optional argument of installName gives origin of name declaration if different from first argument *)
  val installName  : IDs.mid * IDs.cid * (IDs.cid option) * string list -> unit
  val installNameC :           IDs.cid * (IDs.cid option) * string list -> unit
  val uninstallName: IDs.mid * string list -> unit

  (* map between namespace prefixes and namespace identifiers (URIs) *)
  (* add (prefix,namespace) pair, prefix must be undeclared *)
  val installPrefix: string * string -> unit
  (* return namespace for a prefix *)
  val lookupPrefix : string -> string option
  (* return most recent prefix for a namespace *)
  val getPrefix    : string -> string option
  
  (* nameLookup and nameLookup' return NONE if a name without module component is undefined
     on all other failures, they raise exceptions with specific error message *)
  (* concepts a name may be refer to *)
  datatype Concept = SIG | VIEW | REL | CON | STRUC
  (* looks up a qualified name relative to a module, checks result against expected concepts *)
  val nameLookup  : Concept list -> IDs.mid * string list -> IDs.cid option
  (* convenience: relative to current target signature, expect anything *)
  val nameLookup' : string list -> IDs.cid option
  (* convenience for non-modular code: relative to current target signature, expect constants, raises no exceptions *)
  val nameLookupC : string list -> IDs.cid option

  (* shadowing of (only) toplevel constants must be allowed for backwards compatibility *)
  (* true if shadowed by later symbol name; if a constant shadows a struct, the struct's components are not shadowed *)
  val isShadowed : IDs.cid -> bool
  
  (* maps global declaration id's to their fixities, Nonfix if undefined *)
  val installFixity : IDs.cid * Fixity.fixity -> unit
  val fixityLookup : IDs.cid -> Fixity.fixity

  (* maps global declaration id's to their name preferences *)
  val installNamePref : IDs.cid * (string list * string list) -> unit
  val namePrefLookup : IDs.cid -> (string list * string list) option

  (* resets the above mappings *)
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
