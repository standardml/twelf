signature ELAB =
sig
  exception Error of string
  exception UndefinedMorph of IDs.mid * IDs.cid    (* raised if partially defined views cannot be applied *)

  (* type checking modular data types *)
  (* checks a SigIncl *)
  val checkModIncl: ModSyn.ModIncl -> unit
  (* checks a StrDec *)
  val checkStrDec : ModSyn.StrDec -> unit
  (* checks a morphism against domain and codomain signature *)
  val checkMorph  : ModSyn.Morph * IDs.mid * IDs.mid -> unit 

  (* called to flatten a structure declaration
     - computes all declarations imported by the structure to the codomain signature (in the order declared in the domain)
     - calls the functions passed as argument on the computed symbol declarations
  *)
  (* precondition: It is assumed that flatten is called after a structAdd is called,
     but before Names.installName is called on the structure's name.
     This is necessary because ill-typed structure declarations are caught only during the flattening, not during structAdd.
     It would be better if structAdd called flatten already, but this way eases integration with the existing Twelf code.
  *)
  val flatten    : IDs.cid * (IDs.cid * IntSyn.ConDec -> IDs.cid) * (IDs.cid * ModSyn.StrDec -> IDs.cid) -> unit
  
  (* apply a morphism to a term *)
  val applyMorph : IntSyn.Exp * ModSyn.Morph -> IntSyn.Exp
end