(* Indexing *)
(* Author: Brigitte Pientka *)

signature TABLEINDEX =
sig

  (*! structure IntSyn : INTSYN !*)
  (*! structure CompSyn : COMPSYN !*)
    
  type answer = {solutions : ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list,
		 lookup: int}

  datatype Strategy = Variant | Subsumption

  val strategy  : Strategy ref 

  val termDepth  : int option ref
  val ctxDepth   : int option ref
  val ctxLength  : int option ref
  val strengthen : bool ref

  val query : (IntSyn.dctx * IntSyn.dctx  * IntSyn.Exp * IntSyn.Sub * (CompSyn.pskeleton -> unit)) option ref

  datatype answState = New | Repeated

  (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *) 
  val table : ((int ref * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp) * answer) list ref 

  val noAnswers : ((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp) * answer) list -> bool

  (* call check/insert *)

  (* callCheck (G, D, U)
   *
   * if D, G |- U     in table  
   *    then SOME(entries)
   * if D, G |- U not in table 
   *    then NONE  
   *          SIDE EFFECT: D, G |- U added to table
   *)

  val callCheck : IntSyn.dctx * IntSyn.dctx * IntSyn.Exp ->  
                  (((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp) * answer) list) option
  

  (* answer check/insert *)
  (* answerCheck (G, D, (U,s))
   * 
   * Assumption: D, G |- U is in table
   *             and A represents the corresponding solutions
   * 
   * G |- s : D, G
   * Dk, G |- sk : D, G
   *
   * If  (Dk, sk) in A then repeated
   *  else New
   *)

  val answerCheck : IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Sub * CompSyn.pskeleton -> answState

  (* reset table *)
  val reset: unit -> unit
  
  val printTable : unit -> unit
  val printTableEntries : unit -> unit

  (* updateTable 
   *
   * SIDE EFFECT: 
   *   for each table entry: 
   *       advance lookup pointer
   *
   * if Table did not change during last stage 
   *    then updateTable () =  false
   * else updateTable () = true
   *)
   
  val updateTable : unit -> bool

  val solutions : answer -> ((IntSyn.dctx * IntSyn.Sub) * CompSyn.pskeleton) list
  val lookup : answer -> int

end;  (* signature TABLEINDEX *)

