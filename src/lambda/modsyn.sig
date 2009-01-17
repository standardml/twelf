(* Syntax for elaborated modules *)
(* Author: Florian Rabe *)

signature MODSYN =
sig
  exception Error of string
  structure I : INTSYN

  (* convenience methods to access components of a structure declaration *)
 (* the datatype for structure declarations *)
  datatype Morph = MorStr of IDs.cid
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  datatype StrDec = StrDec of
    string                             (* name *)
    * IDs.qid                          (* qualified local id *)
    * IDs.mid                              (* domain (= instantiated module) *)
    * SymInst list                     (* instantiations *)
    
  val strDecName   : StrDec -> string
  val strDecDomain : StrDec -> IDs.mid


  val sgnReset : unit -> unit
  val sgnAdd   : IDs.mid * I.ConDec -> IDs.cid 
  val sgnAddC  : I.ConDec -> IDs.cid
  val sgnLookup: IDs.cid -> I.ConDec
  val sgnApp   : IDs.mid * (IDs.cid -> unit) -> unit
  val sgnAppC  : (IDs.cid -> unit) -> unit
  val modApp   : (IDs.mid -> unit) -> unit
  (* the current module *)
  val currentMod : unit -> IDs.mid
  (* maps local id's in the current module to global id's *)
  val inCurrent : IDs.lid -> IDs.cid

  (* adds a strucutre constant declaration to a module *)
  val structAdd    : IDs.mid * StrDec -> IDs.cid
  (* looks up a structure by global id *)
  val structLookup : IDs.cid -> StrDec

  (* convenience methods to access components of an installed constant declaration *)
  val constType   : IDs.cid -> I.Exp		(* type of c or d             *)
  val constDef    : IDs.cid -> I.Exp		(* definition of d            *)
  val constImp    : IDs.cid -> int
  val constStatus : IDs.cid -> I.Status
  val constUni    : IDs.cid -> I.Uni
  val constBlock  : IDs.cid -> I.dctx * I.Dec list

  (* Expanding type definitions *)
  val targetFamOpt : I.Exp -> IDs.cid option  (* target type family or NONE *)
  val targetFam : I.Exp -> IDs.cid            (* target type family         *)
end
