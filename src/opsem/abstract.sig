(* Abstraction *)
(* Author: Brigitte Pientka *)

signature ABSTRACTTABLED =
sig
  (*! structure IntSyn : INTSYN !*)

  exception Error of string

  val strengthen : bool ref

  val abstractEVarCtx : (IntSyn.dctx * IntSyn.Exp * IntSyn.Sub) ->  
                        (IntSyn.dctx * IntSyn.dctx * IntSyn.Exp * IntSyn.Sub)


  val abstractAnswSub : IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub

  val abstractAnsw : IntSyn.dctx * IntSyn.Sub -> IntSyn.dctx * IntSyn.Sub 

  val raiseType : IntSyn.dctx * IntSyn.Exp -> IntSyn.Exp   


end;  (* signature ABSTRACTTABLED *)
