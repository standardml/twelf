(* Indexing *)
(* Author: Brigitte Pientka *)

signature TABLEINDEX =
sig

  structure IntSyn : INTSYN
    
  type answer = {solutions : (IntSyn.dctx * IntSyn.Sub) list,
		 lookup: int}

  datatype Strategy = Variant | Subsumption

  val strategy  : Strategy ref 

  val termDepth : int option ref
  val strengthen : bool ref

  datatype answState = new | repeated

  (* table: G, Gdprog |- goal , 
            (answ list (ith stage) , answ list (1 to i-1 th stage))
   *) 
  val table : ((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp) * answer) list ref 

  val noAnswers : ((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp) * answer) list -> bool

  (* call check/insert *)

  (* callCheck (Gdp, G, M, U)
   *
   * if Gdp, G |= _ : U     in table  
   *    then SOME(entries)
   * if Gdp, G |= U not in table 
   *    then NONE  
   *          SIDE EFFECT: Gdp, G |= M : U added to table
   *)

  val callCheck : IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp ->  
                  (((IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Exp) * answer) list) option
  

  (* answer check/insert *)
  (* answerCheck (Gdp, G, (U,s), M)
   * 
   * Assumption: Gdp, G |= U is in table
   *             and S represents the corresponding solutions
   *
   * If  s in S then repeated
   *  else new
   *)

  val answerCheck : IntSyn.dctx * IntSyn.dctx * 
                    (IntSyn.Exp * IntSyn.Exp) * IntSyn.Sub  -> answState

  (* reset table *)
  val reset: unit -> unit
  
  val printTable : unit -> unit

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

  val solutions : answer -> (IntSyn.dctx * IntSyn.Sub) list
  val lookup : answer -> int

end;  (* signature TABLEINDEX *)

