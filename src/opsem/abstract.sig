(* Abstraction *)
(* Author: Brigitte Pientka *)

signature ABSTRACTTABLED =
sig

  (*! structure IntSyn : INTSYN !*)

  (*! structure TableParam : TABLEPARAM !*)
    
  exception Error of string


  val abstractEVarCtx : (CompSyn.DProg * IntSyn.Exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * TableParam.ResEqn * IntSyn.Sub)

  val abstractAnswSub :  IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub  

  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp   

end;  (* signature ABSTRACTTABLED *)
