(* Syntax and semantics of the module system, also encapsulation of the state of modular LF *)
(* Author: Florian Rabe *)

signature MODSYN =
sig
  exception Error of string
  structure I : INTSYN

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
     a morphism from S to T can be regarded as an expression of type S over signature T
  *)
  datatype Morph = MorStr of IDs.cid | MorView of IDs.mid
  (*
     symbol instantiations
     instantiations are the building blocks of structures and views, say from S to T
     ConInst(c, t) instantiates the constant c of S with the expression t over T
     StrInst(i, m) instantiates the structure i (say with domain R) of S with the expression m, i.e., a morphism from R to T
  *)
  datatype SymInst = ConInst of IDs.cid * I.Exp | StrInst of IDs.cid * Morph
  
  (*
     structure declarations
     a structure declared instantiates another signature, say S
     such a structure i declared in signature T induces a morphism MorStr(i) from S to T
     such a structure carries instantiations of symbols of S with expressions of T
  *)
  datatype StrDec = StrDec of
    string list                        (* qualified name *)
    * IDs.qid                          (* list of structures via which it is imported *)
    * IDs.mid                          (* domain (= instantiated signature) *)
    * SymInst list                     (* instantiations *)
    
  (*
     signature declarations
     a signature is a list of symbol declarations
     the declarations of a signtature are stored separately and are not part of the SigDec
  *)
  datatype SigDec = SigDec of
    string list                        (* qualified name *)

  (*
     view declarations
     a view from S to T provides instantiations for all symbols of S in terms of expressions over T
     it can be considered as an implementation of S in terms of the symbols of T
     thus a view from S to T can be seen as a functor from T to S
     the instantiations of a view are stored separately and are not part of the ViewDec
  *)
  datatype ViewDec = ViewDec of
    string list                        (* qualified name *)
    * IDs.mid                          (* domain *)
    * IDs.mid                          (* codomain *)
    
  (* convenience methods to access components of declarations *)
  val strDecName   : StrDec -> string list
  val strDecDomain : StrDec -> IDs.mid

  (********************** Interface methods that affect the state **********************)
  
  (* called at the beginning of a module *)
  val modOpen    : unit -> IDs.mid
  (* called at the end of a module *)
  val modClose   : unit -> unit
  (* called to add a constant declaration to a signature *)
  val sgnAdd     : IDs.mid * I.ConDec -> IDs.cid 
  val sgnAddC    : I.ConDec -> IDs.cid
  (* called to add a structure declaration to a signature *)
  val structAdd  : IDs.mid * StrDec -> IDs.cid
  val structAddC : StrDec -> IDs.cid
  (* called to reset the state *)
  val reset      : unit -> unit

  (* flattens a structure declaration
     - computes all declarations imported by the structure to the codomain signature (in the order declared in the domain)
     - calls the functions passed as argument on the computed symbol declarations
  *)
  (* precondition: It is assumed that flatten is called after a structAdd is called,
     but before Names.installName is called on the structure's name.
     This is necessary because ill-typed structure declarations are caught only during the flattening.
     This is not a design feature of the module system per se, but a compromise to ease integration with the existing Twelf code.
  *)
  val flatten    : IDs.cid * (I.ConDec -> unit) * (StrDec -> unit) -> unit

  (********************** Interface methods that do not affect the state **********************)
  
  (* look up of constant declarations by global id *)
  val sgnLookup  : IDs.cid -> I.ConDec
  (* look up structure declarations by global id *)
  val structLookup: IDs.cid -> StrDec
  (* application of a method to all constants of a signature in declaration order *)
  val sgnApp     : IDs.mid * (IDs.cid -> unit) -> unit
  val sgnAppC    : (IDs.cid -> unit) -> unit
  (* application of a method to all modules in declaration order *)
  val modApp     : (IDs.mid -> unit) -> unit
  (* the current module *)
  val currentMod : unit -> IDs.mid
  (* maps local id's in the current module to global id's *)
  val inCurrent  : IDs.lid -> IDs.cid

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
