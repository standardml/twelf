structure MetaSyn = 
  MetaSyn ((*! structure IntSyn' = IntSyn !*)
	   structure Whnf = Whnf);

structure MetaAbstract = 
  MetaAbstract (structure Global = Global
                structure MetaSyn' = MetaSyn
		structure MetaGlobal = MetaGlobal
		structure Abstract = Abstract
		structure ModeTable = ModeTable
		structure Whnf = Whnf
		structure Print = Print
		structure Constraints = Constraints
		structure Unify = UnifyNoTrail
		structure Names = Names
		structure TypeCheck = TypeCheck
		structure Subordinate = Subordinate
                (*! structure CSManager = CSManager !*)
		  );

structure MetaPrint = 
  MetaPrint (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure Formatter = Formatter
	     structure Print = Print
	     structure ClausePrint = ClausePrint);

structure Init = 
  Init (structure MetaSyn' = MetaSyn
	structure MetaAbstract = MetaAbstract);

structure OLDSearch = 
  OLDSearch (structure MetaGlobal = MetaGlobal
	  structure Conv = Conv
	  structure MetaSyn' = MetaSyn
	  (*! structure CompSyn' = CompSyn !*)
	  structure Compile = Compile
	  structure Whnf = Whnf
	  structure Unify = UnifyTrail
	  structure Index = IndexSkolem
	  (* structure Assign = Assign *)
	  structure CPrint = CPrint
	  structure Print = Print
	  structure Names = Names
          (*! structure CSManager = CSManager !*)
	    );

structure Lemma =
  Lemma (structure MetaSyn' = MetaSyn
	 structure MetaAbstract = MetaAbstract);

structure Splitting =
  Splitting (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure MetaPrint = MetaPrint
	     structure MetaAbstract = MetaAbstract
	     structure Whnf = Whnf
	     structure ModeTable = ModeTable
	     structure Index = Index
	     structure Print = Print
	     structure Unify = UnifyTrail
             (*! structure CSManager = CSManager !*)
	       );

structure Filling =
  Filling (structure Global = Global
	   structure MetaSyn' = MetaSyn
	   structure MetaAbstract = MetaAbstract
	   structure Print = Print
	   structure Search = OLDSearch
	   structure Whnf = Whnf);

structure Recursion =
  Recursion (structure Global = Global
	     structure MetaSyn' = MetaSyn
	     structure MetaPrint = MetaPrint
	     structure Whnf = Whnf
	     structure Unify = UnifyTrail
	     structure Conv = Conv
	     structure Names = Names
	     structure Print = Print
	     structure Subordinate = Subordinate
	     structure Order = Order
	     structure ModeTable = ModeTable
	     structure MetaAbstract = MetaAbstract
	     structure Lemma = Lemma
	     structure Filling = Filling
	     structure Formatter = Formatter
             (*! structure CSManager = CSManager !*)
	       );

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
	  structure Filling = Filling
	  structure Splitting = Splitting
	  structure Recursion = Recursion
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

structure Skolem = 
  Skolem (structure Global = Global
          (*! structure IntSyn' = IntSyn !*)
	  structure Whnf = Whnf
	  structure Abstract = Abstract
	  structure IndexSkolem = IndexSkolem
	  structure ModeTable = ModeTable
	  structure Print = Print
	  structure Timers = Timers
	  structure Compile = Compile
	  structure Names = Names);