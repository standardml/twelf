(* Reasoning about orders *)
(* Author: Brigitte Pientka *)

signature CHECKING =
sig
  (*! structure IntSyn : INTSYN !*)
  structure Order : ORDER
  (*! structure Paths : PATHS !*)
    
  (* If Q marks all parameters in a context G we write   G : Q  *)

  datatype Quantifier =        (* Quantifier to mark parameters *)
    All                  (* Q ::= All                     *)
  | Exist                (*     | Exist                     *)
  | And of Paths.occ     (*     | And                     *)


  datatype 'a Predicate = 
    Less of 'a * 'a
  | Leq of 'a * 'a 
  | Eq of 'a * 'a 
  | Pi of IntSyn.Dec * 'a Predicate        
    

  type order = (IntSyn.eclo * IntSyn.eclo) Order.Order 

  (* reduction predicate context (unordered) *)
  type rctx = order Predicate list


  (* mixed-prefix context *)
  type qctx = Quantifier IntSyn.Ctx

  val shiftRCtx : rctx -> (IntSyn.Sub -> IntSyn.Sub) -> rctx

  val shiftPred : order Predicate ->  (IntSyn.Sub -> IntSyn.Sub) 
                  -> order Predicate
   
  val deduce : IntSyn.dctx * qctx * rctx * order Predicate -> bool
 
end;  (* signature CHECKING *)
