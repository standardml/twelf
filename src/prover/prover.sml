structure State = State 
  ((*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure WorldSyn' = WorldSyn
   structure Normalize = Normalize)
     
structure StatePrint = StatePrint 
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Names = Names
   structure Formatter' = Formatter
   structure Print = Print
   structure TomegaPrint = TomegaPrint)

structure Introduce = Introduce 
  ((*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State)

structure FixedPoint = FixedPoint 
  ((*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Normalize = Normalize)

structure Split = Split
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Normalize = Normalize
   structure Whnf = Whnf
   structure Abstract = Abstract
   structure Unify = UnifyTrail
   structure Constraints = Constraints
   structure Index = Index
   structure Names = Names
   structure Print = Print
   structure TypeCheck = TypeCheck
   structure Subordinate = Subordinate)


structure Search = Search 
  (structure Global = Global
   structure MTPGlobal = MTPGlobal
   (*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Abstract = Abstract
   structure Conv = Conv
   structure CompSyn' = CompSyn
   structure Compile = Compile
   structure Whnf = Whnf
   structure Unify = UnifyTrail
   structure Index = IndexSkolem
   structure Assign = Assign 
   structure CPrint = CPrint
   structure Print = Print
   structure Names = Names
   structure CSManager = CSManager); 

structure Fill = Fill
  (structure MTPGlobal = MTPGlobal
   structure MTPData = MTPData
   (*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Normalize = Normalize
   structure Whnf = Whnf
   structure Abstract = Abstract
   structure Unify = UnifyTrail
   structure Constraints = Constraints
   structure Index = Index
   structure Search = Search
   structure TypeCheck = TypeCheck)

structure Interactive = Interactive
  (structure Global = Global
   (*! structure IntSyn' = IntSyn !*)
   (*! structure Tomega' = Tomega !*)
   structure State' = State
   structure Ring = Ring
   structure Formatter = Formatter
   structure Names = Names
   structure Weaken = Weaken
   structure ModeSyn = ModeSyn
   structure WorldSyn = WorldSyn
   structure StatePrint = StatePrint
   structure Introduce = Introduce
   structure FixedPoint = FixedPoint
   structure Split = Split
   structure Fill = Fill)
 