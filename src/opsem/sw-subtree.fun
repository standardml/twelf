functor SwMemoTable ((* structure TableParam : TABLEPARAM *)
                     structure MemoTable : MEMOTABLE
                     structure MemoTableInst : MEMOTABLE
                     (*! sharing MemoTableInst.IntSyn = MemoTable.IntSyn !*)
                     (*! sharing MemoTableInst.CompSyn = MemoTable.CompSyn !*)
                     (*! sharing MemoTableInst.TableParam = MemoTable.TableParam !*)
                       ) : MEMOTABLE =
struct

  (*! structure IntSyn = MemoTable.IntSyn !*)
  (*! structure CompSyn = MemoTable.CompSyn !*)
  (*! structure TableParam = MemoTable.TableParam !*)


  fun callCheck args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.callCheck args
    | TableParam.Subsumption => MemoTableInst.callCheck args


  fun insertIntoTree args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.insertIntoTree args
    | TableParam.Subsumption => MemoTableInst.insertIntoTree args

  fun answerCheck args =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.answerCheck args
    | TableParam.Subsumption => MemoTableInst.answerCheck args


  fun reset () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.reset ()
    | TableParam.Subsumption => MemoTableInst.reset ()

  fun updateTable () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.updateTable ()
    | TableParam.Subsumption => MemoTableInst.updateTable ()

  fun tableSize () =
    case (!TableParam.strategy)
      of TableParam.Variant => MemoTable.tableSize ()
    | TableParam.Subsumption => MemoTableInst.tableSize ()


  fun memberCtx args =
    case (!TableParam.strategy) of
      TableParam.Subsumption => MemoTableInst.memberCtx args
    | TableParam.Variant => MemoTable.memberCtx args

end;  (* functor SwMemoTable *)

