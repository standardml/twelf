(* Syntax for elaborated modules *)
(* Author: Florian Rabe *)

signature MODSYN =
sig
  exception Error of string
  structure I : INTSYN

  datatype Morph = MorStr of IDs.cid
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  (* a structure declaration instantiates a module with a list of assignments of expressions to qids *)
  datatype StrDec = StrDec of
    string list                        (* qualified name *)
    * IDs.qid                          (* qualified local id *)
    * IDs.mid                          (* domain (= instantiated module) *)
    * SymInst list                     (* instantiations *)
    
  (* convenience methods to access components of a structure declaration *)
  val strDecName   : StrDec -> string list
  val strDecDomain : StrDec -> IDs.mid

  val modOpen : unit -> IDs.mid
  val modClose : unit -> unit
  val reset : unit -> unit
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
  val structAddC   : StrDec -> IDs.cid
  (* looks up a structure by global id *)
  val structLookup : IDs.cid -> StrDec
  
  (* flatten a structure declaration *)
  val flatten      : IDs.cid * (I.ConDec -> unit) * (StrDec -> unit) -> unit

  (* convenience methods to access components of an installed constant declaration *)
  val constType   : IDs.cid -> I.Exp		(* type of c or d             *)
  val constDef    : IDs.cid -> I.Exp		(* definition of d            *)
  val constImp    : IDs.cid -> int
  val constStatus : IDs.cid -> I.Status
  val constUni    : IDs.cid -> I.Uni
  val constBlock  : IDs.cid -> I.dctx * I.Dec list

  (* These might also be in IntSyn.fun. But they must be here because they need to look up and expand type definitions. *)
  val ancestor : I.Exp -> I.Ancestor
  val defAncestor : IDs.cid -> I.Ancestor
  val targetFamOpt : I.Exp -> IDs.cid option  (* target type family or NONE *)
  val targetFam : I.Exp -> IDs.cid            (* target type family         *)
end
