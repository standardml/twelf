(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

signature STATE =
sig
  exception Error of string

  datatype State =
    State of Tomega.Worlds 
      * Tomegas.Dec IntSyn.Ctx * Tomega.Prg * Tomega.For	
  | StateLF of IntSyn.Exp

  datatype Focus = 
    Focus of Tomega.Prg * Tomega.Worlds (* Focus (EVar, W) *)
  | FocusLF of IntSyn.Exp	        (* focus EVar *)
 
  val init : Tomega.For * Tomega.Worlds -> State
  val close : State -> bool  

  val collectT  : Tomega.Prg -> Tomega.Prg list
  val collectLF : Tomega.Prg -> IntSyn.Exp list
  val collectLFSub : Tomega.Sub -> IntSyn.Exp list
end