(* External syntax for module expressions *)
(* Author: Kevin Watkins *)

signature MODEXTSYN =
sig

  structure ExtSyn : EXTSYN
  (*! structure Paths : PATHS !*)

  type strexp
  val strexp : string list * string * Paths.region -> strexp

  type inst
  val coninst : (string list * string * Paths.region)
                  * ExtSyn.term * Paths.region -> inst
  val strinst : (string list * string * Paths.region)
                  * strexp * Paths.region -> inst

  type sigexp
  val thesig : sigexp
  val sigid : string * Paths.region -> sigexp
  val wheresig : sigexp * inst list -> sigexp

  type sigdef
  val sigdef : string option * sigexp -> sigdef

  type structdec
  val structdec : string option * sigexp -> structdec
  val structdef : string option * strexp -> structdec

end;

signature RECON_MODULE =
sig

  include MODEXTSYN
  structure ModSyn : MODSYN

  exception Error of string

  type whereclause

  datatype StructDec =
      StructDec of string option * ModSyn.module * whereclause list
    | StructDef of string option * IntSyn.mid

  val strexpToStrexp : strexp -> IntSyn.mid
  val sigexpToSigexp : sigexp * ModSyn.module option -> ModSyn.module * whereclause list
  val sigdefToSigdef : sigdef * ModSyn.module option
                         -> string option * ModSyn.module * whereclause list
  val structdecToStructDec : structdec * ModSyn.module option -> StructDec

  val moduleWhere : ModSyn.module * whereclause -> ModSyn.module

end
