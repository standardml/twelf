(* State definition for Proof Search *)
(* Author: Carsten Schuermann *)

signature STATE =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA !*)

  exception Error of string

  datatype State =
    State of (Tomega.Dec IntSyn.Ctx * Tomega.For)
           * Tomega.Worlds

  val init : Tomega.For * Tomega.Worlds -> State
  val close : State -> bool  

  val construct : State              
                  -> (Tomega.Prg -> Tomega.Prg)      (* Success continuation *)
                  -> (unit -> Tomega.Prg)            (* Failure continuation *)
                  -> Tomega.Prg
end