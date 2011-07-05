signature ELAB =
sig
  exception Error of string
  (* raised if a partially defined view/relation cannot be applied
      within the module: an expected type for a case cannot be computed because it depends on a missing case
      at the end of a module: the module is not total
      when the view is used: a previous MissingCase was recovered from by accepting a partial module *)
  exception MissingCase of IDs.mid * IDs.cid * string

  (* type checking modular data types *)
  (* checks a ModDec *)
  val checkModBegin : ModSyn.ModDec -> unit
  val checkModEnd   : IDs.mid -> unit
  (* checks a SigIncl *)
  val checkSigIncl: ModSyn.SigIncl -> unit
  (* checks a StrDec *)
  val checkStrDec : ModSyn.StrDec -> ModSyn.StrDec
  
  (* checks declarations in a view *)
  val checkSymInst: ModSyn.SymInst -> ModSyn.SymInst
  (* checks a morphism against domain and codomain signature, returns reconstructed morphism *)
  val checkMorph  : ModSyn.Morph * IDs.mid * IDs.mid -> ModSyn.Morph
  (* infers domain and codomain, fills in implicit coercions, raises Error if not composable *)
  val reconMorph  : ModSyn.Morph -> IDs.mid * IDs.mid * ModSyn.Morph
  (* apply a morphism to a term *)
  val applyMorph : IntSyn.Exp * ModSyn.Morph -> IntSyn.Exp

  (* checks declarations in a logical relation *)
  val checkSymCase : ModSyn.SymCase -> ModSyn.SymCase
  (* checks a logical relation against domain, codomain, and morphisms, returns reconstructed morphism *)
  val checkRel  : ModSyn.Rel * IDs.mid * IDs.mid * (ModSyn.Morph list) -> ModSyn.Rel
  (* infers domain, codomain and morphisms of a logical relation *)
  val reconRel  : ModSyn.Rel -> IDs.mid * IDs.mid * (ModSyn.Morph list) * ModSyn.Rel

  (* apply a logical relation to a term *)
  val applyRel   : IntSyn.Exp * IntSyn.Exp option * ModSyn.Rel -> IntSyn.Exp
  (* expType(c,rel) the expected type of rel(c) *)
  val expType    : IDs.cid * ModSyn.Rel -> IntSyn.Exp

  (* called to flatten a structure declaration in a signature, view, or logical relation
     - computes all declarations imported by the structure to the codomain signature (in the order declared in the domain)
     - calls the functions passed as argument on the computed symbol declarations
  *)
  (* precondition: It is assumed that flatten is called after a structAdd is called,
     but before Names.installName is called on the structure's name.
     This is necessary because ill-typed structure declarations are caught only during the flattening, not during structAdd.
     It would be better if structAdd called flatten already, but this way eases integration with the existing Twelf code.
  *)
  val flattenDec    : IDs.cid * (IDs.cid * IntSyn.ConDec -> IDs.cid) * (IDs.cid * ModSyn.StrDec -> IDs.cid) -> unit
  val flattenInst   : IDs.cid * (ModSyn.SymInst -> IDs.cid) -> unit
  val flattenCase   : IDs.cid * (ModSyn.SymCase -> IDs.cid) -> unit
end