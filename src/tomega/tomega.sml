structure TomegaAbstract = TomegaAbstract 
  (structure Global = Global
   structure Abstract = Abstract
   structure Whnf = Whnf
   structure Subordinate = Subordinate);
  

structure TomegaPrint = TomegaPrint
  ((*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure Formatter = Formatter
   structure Names = Names
   structure Print = Print)

structure TomegaTypeCheck = TomegaTypeCheck
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   structure Abstract = Abstract
   (*! structure Tomega' = Tomega !*)
   structure TypeCheck = TypeCheck
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken
   structure TomegaAbstract = TomegaAbstract);

(* structure TomegaUnify = TomegaUnify
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   structure Abstract = Abstract
   (*! structure Tomega' = Tomega !*)
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Conv = Conv
   structure Whnf = Whnf
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure Print = Print
   structure Weaken = Weaken);
*)


structure Opsem = Opsem
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Unify = UnifyNoTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Print = Print
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Weaken = Weaken);

(*
structure Opsem = OpsemCont
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure TypeCheck = TypeCheck
   structure Normalize = Normalize
   structure Unify = UnifyNoTrail
   structure Conv = Conv
   structure Whnf = Whnf
   structure Print = Print
   structure Subordinate = Subordinate
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Weaken = Weaken);
*)

structure Redundant = Redundant
  (structure Opsem = Opsem)


structure Converter = Converter
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Abstract = Abstract
   structure Tomega' = Tomega
   structure Names = Names
   structure ModeTable = ModeTable
   structure TypeCheck = TypeCheck
   structure TomegaAbstract = TomegaAbstract
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Trail = Trail
   structure Unify = UnifyTrail
   structure TomegaPrint = TomegaPrint
   structure Whnf = Whnf
   structure WorldSyn = WorldSyn
   structure Worldify = Worldify
   structure Subordinate = Subordinate
   structure Print = Print
   structure Redundant = Redundant
   structure Weaken = Weaken);


structure TomegaCoverage = TomegaCoverage
  (structure Global = Global
   structure IntSyn' = IntSyn
   structure Tomega' = Tomega
   structure TomegaPrint = TomegaPrint
   structure TomegaTypeCheck = TomegaTypeCheck
   structure Cover = Cover);
