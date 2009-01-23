(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)

signature MODSYN =
sig
  structure I : INTSYN

  exception Error of string           (* raised on general errors *)
  exception UndefinedCid of IDs.cid   (* raised when symbol lookups fail *)
  exception UndefinedMid of IDs.mid   (* raised when module lookups fail *)


  (* general notes
     The concept of modules unifies the concepts of signatures and views.
     The concept of symbols unifies the concepts of constants (i.e., ConDec) and structures (i.e., StrDec).
     The concept of links unifies the concept of structures and views.
     A "C" at the end of a function name means that it affects the current module (i.e., the most recently opened one).
     Besides IntSyn, only the global structure IDs is assumed. In particular, we have
     - mid: module id (nested modules have unique mids)
     - cid: global symbol id, every constant or structure of any module has a unique cid
  *)

  (********************** Data types and related functions **********************)
  
  (*
     morphisms
     morphisms have a domain and a codomain signature
     a morphism from S to T can be regarded as a (structure) expression of type S over signature T
     MorStr(c) is the morphism induced by the structure c
     MorView(m) is the morphism induced by the view m
     MorComp(mor,mor') is the composition of mor and mor' in diagram order (i.e., mor' o mor)
  *)
  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid | MorComp of Morph * Morph
  
  (*
     symbol instantiations
     instantiations are the building blocks of structures and views, say from S to T
     ConInst(c, t) instantiates the constant c of S with the expression t over T
     StrInst(r, mor) instantiates the structure r (say with domain R) of S with the expression mor,
        i.e., a morphism from R to T
     deep assignments are possible, e.g., ConInst(r.s.c, t) or Str(r.s, mor)
  *)
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  
  (*
     structure declarations
     a structure instantiates another signature, say S
     such a structure s declared in signature T induces a morphism MorStr(s) from S to T
     such a structure carries instantiations of symbols of S with expressions of T
     structure definitions define a structure with a morphism
  *)
  datatype StrDec
  = StrDec of
      string list                      (* qualified name *)
    * IDs.qid                          (* list of structures via which it is imported *)
    * IDs.mid                          (* domain (= instantiated signature) *)
    * SymInst list                     (* instantiations *)
  | StrDef of
      string list                      (* qualified name *)
    * IDs.qid                          (* list of structures via which it is imported *)
    * IDs.mid                          (* domain (= instantiated signature) *)
    * Morph                            (* definition *)    
  (* unifies constant and structure declarations *)
  datatype SymLevelData = SymCon of I.ConDec | SymStr of StrDec | SymConInst of SymInst | SymStrInst of SymInst
    
  (*
     signature declarations
     a signature is a list of symbol declarations
     the declarations of a signtature are stored separately and are not part of the SigDec
  *)
  (*
     view declarations
     a view from S to T provides instantiations for all symbols of S in terms of expressions over T
     it can be considered as an implementation of S in terms of the symbols of T
     thus a view from S to T can be seen as a functor from T to S
     the instantiations of a view are stored separately and are not part of the ViewDec
  *)
  datatype ModDec
     = SigDec of string list           (* qualified name *)
     | ViewDec of
         string list                   (* name *)
       * IDs.mid                       (* domain *)
       * IDs.mid                       (* codomain *)
    

  (* convenience methods to access components of declarations *)
  val modDecName : ModDec -> string list
  val strDecName : StrDec -> string list
  val strDecFoldName: StrDec -> string
  val strDecQid  : StrDec -> IDs.qid
  val strDecDom  : StrDec -> IDs.mid
  val symInstCid : SymInst -> IDs.cid
  val modName    : IDs.mid -> string list
  val modFoldName: IDs.mid -> string
  val symName    : IDs.cid -> string list
  val symFoldName: IDs.cid -> string  
  val symQid     : IDs.cid -> IDs.qid

  (********************** Interface methods that affect the state **********************)
  
  (* called at the beginning of a module *)
  val modOpen    : ModDec -> IDs.mid
  (* called at the end of a module *)
  val modClose   : unit -> unit
  (* called to add a constant declaration to the current signature, which must be a signature *)
  val sgnAddC    : I.ConDec -> IDs.cid
  (* called to add a structure declaration to the current module, which must be a signature *)
  val structAddC : StrDec -> IDs.cid
  (* called to add an instantiation to the current module, which must be a view *)
  val instAddC   : SymInst -> IDs.cid
  (* called to reset the state *)
  val reset      : unit -> unit

  (* called to flatten a structure declaration
     - computes all declarations imported by the structure to the codomain signature (in the order declared in the domain)
     - calls the functions passed as argument on the computed symbol declarations
  *)
  (* precondition: It is assumed that flatten is called after a structAdd is called,
     but before Names.installName is called on the structure's name.
     This is necessary because ill-typed structure declarations are caught only during the flattening, not during structAdd.
     It would be better if structAdd called flatten already, but this way eases integration with the existing Twelf code.
  *)
(*  val flatten    : IDs.cid * (IDs.cid * I.ConDec -> IDs.cid) * (IDs.cid * StrDec -> IDs.cid) -> unit
  remove --cs *)
  (********************** Interface methods that do not affect the state **********************)

  (* generic lookup of symbol declarations or instantiation by global id, raises (UndefinedCid c) *)
  val symLookup : IDs.cid -> SymLevelData
  (* specialized lookups; these raise (UndefinedCid _) if the cid is defined but returns the wrong data *)
  val sgnLookup     : IDs.cid -> I.ConDec          (* constant declarations *)
  val structLookup  : IDs.cid -> StrDec            (* structure declarations *)
  val conInstLookup : IDs.cid -> SymInst           (* constant instantiations *)
  val strInstLookup : IDs.cid -> SymInst           (* structure instantiations *)

  val onToplevel : unit -> bool
  val modLookup  : IDs.mid -> ModDec
  val modParent  : IDs.mid -> IDs.mid option
  (* application of a method to all constants of a signature in declaration order *)
  val sgnApp     : IDs.mid * (IDs.cid -> unit) -> unit
  val sgnAppC    : (IDs.cid -> unit) -> unit
  (* application of a method to all modules in declaration order *)
  val modApp     : (IDs.mid -> unit) -> unit
  (* the current module *)
  val currentMod : unit -> IDs.mid
  (* true: current module is signature, false: current module is view *)
  val inSignature: unit -> bool
  (* the current target signature: the current module if a signature, or its codomain if a view *)
  val currentTargetSig : unit -> IDs.mid
  (* returns the list of currently open modules in declaration order *)
  val getScope   : unit -> IDs.mid list 

  val structMapLookup : IDs.cid * IDs.cid -> IDs.cid option
    

  (* convenience methods to access components of an installed constant declaration *)
  val constType   : IDs.cid -> I.Exp		(* type of c or d *)
  val constDef    : IDs.cid -> I.Exp		(* definition of d *)
  val constImp    : IDs.cid -> int
  val constStatus : IDs.cid -> I.Status
  val constUni    : IDs.cid -> I.Uni
  val constBlock  : IDs.cid -> I.dctx * I.Dec list

  (* These functions are specific to the non-modular syntax (IntSyn), but independent of the module system.
     However, they must be declared after ModSyn because they need to look up and expand type definitions. *)
  val ancestor    : I.Exp -> I.Ancestor
  val defAncestor : IDs.cid -> I.Ancestor
  val targetFamOpt: I.Exp -> IDs.cid option  (* target type family or NONE *)
  val targetFam   : I.Exp -> IDs.cid         (* target type family         *)

end (* signature MODSYN *)
