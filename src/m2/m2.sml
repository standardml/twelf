structure MetaSyn = 
  MetaSyn (structure IntSyn' = IntSyn
	   structure Whnf = Whnf);

structure MetaAbstract = 
  MetaAbstract (structure Global = Global
                structure MetaSyn' = MetaSyn
		structure MetaGlobal = MetaGlobal
		structure Abstract = Abstract
		structure ModeSyn = ModeSyn
		structure Whnf = Whnf
		structure Print = Print
		structure Trail = Trail
		structure Constraints = Constraints
		structure Unify = Unify
		structure Pattern = Pattern
		structure Names = Names
		structure TypeCheck = TypeCheck
		structure Subordinate = Subordinate);

structure MetaPrint = 
  MetaPrint (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure Formatter = Formatter
	     structure Print = Print
	     structure ClausePrint = ClausePrint);

structure Init = 
  Init (structure MetaSyn' = MetaSyn
	structure MetaAbstract = MetaAbstract);

structure Search = 
  Search (structure MetaGlobal = MetaGlobal
	  structure IntSyn' = IntSyn
	  structure Conv = Conv
	  structure MetaSyn' = MetaSyn
	  structure CompSyn' = CompSyn
	  structure Compile = Compile
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail
	  structure Trail = Trail
	  structure CPrint = CPrint
	  structure Print = Print
	  structure Names = Names); 

structure Lemma =
  Lemma (structure MetaSyn' = MetaSyn
	 structure MetaAbstract = MetaAbstract);

structure Splitting =
  Splitting (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure MetaPrint = MetaPrint
	     structure MetaAbstract = MetaAbstract
	     structure ModeSyn = ModeSyn
	     structure Print = Print
	     structure Unify = UnifyTrail);

structure Filling =
  Filling (structure Global = Global
	   structure MetaSyn' = MetaSyn
	   structure MetaAbstract = MetaAbstract
	   structure Print = Print
	   structure Search = Search
	   structure Whnf = Whnf);

structure Recursion =
  Recursion (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure MetaPrint = MetaPrint
	     structure Whnf = Whnf
	     structure Unify = UnifyTrail
	     structure Conv = Conv
	     structure Trail = Trail
	     structure Names = Names
	     structure Print = Print
	     structure Subordinate = Subordinate
	     structure Order = Order
	     structure ModeSyn = ModeSyn
	     structure MetaAbstract = MetaAbstract
	     structure Lemma = Lemma
	     structure Filling = Filling
	     structure Formatter = Formatter);

structure Qed = 
  Qed (structure Global = Global
       structure MetaSyn' = MetaSyn);

structure StrategyFRS = 
  StrategyFRS (structure MetaGlobal = MetaGlobal
	       structure MetaSyn' = MetaSyn
	       structure MetaAbstract = MetaAbstract 
	       structure Lemma = Lemma
	       structure Filling = Filling
	       structure Recursion = Recursion
	       structure Splitting = Splitting
	       structure Qed = Qed
	       structure MetaPrint = MetaPrint
	       structure Timers = Timers);

structure StrategyRFS = 
  StrategyRFS (structure MetaGlobal = MetaGlobal
	       structure MetaSyn' = MetaSyn
	       structure MetaAbstract = MetaAbstract 
	       structure Lemma = Lemma
	       structure Filling = Filling
	       structure Recursion = Recursion
	       structure Splitting = Splitting
	       structure Qed = Qed
	       structure MetaPrint = MetaPrint
	       structure Timers = Timers);

structure Strategy = 
  Strategy (structure MetaGlobal = MetaGlobal
	    structure MetaSyn' = MetaSyn
	    structure StrategyFRS = StrategyFRS
	    structure StrategyRFS = StrategyRFS);

structure Prover = 
  Prover (structure MetaGlobal = MetaGlobal
	  structure MetaSyn' = MetaSyn
	  structure MetaAbstract = MetaAbstract 
	  structure MetaPrint = MetaPrint
	  structure Init = Init
	  structure Strategy = Strategy
	  structure Qed = Qed
	  structure Names = Names
	  structure Timers = Timers);

structure Mpi = 
  Mpi (structure MetaGlobal = MetaGlobal
       structure MetaSyn' = MetaSyn
       structure MetaAbstract = MetaAbstract 
       structure Init = Init
       structure Lemma = Lemma
       structure Filling = Filling
       structure Recursion = Recursion
       structure Splitting = Splitting
       structure Strategy = Strategy
       structure Qed = Qed
       structure MetaPrint = MetaPrint
       structure Names = Names
       structure Timers = Timers
       structure Ring = Ring);
