(* Generic Traversal Intended for Language-Specific Printing *)
(* Author: Frank Pfenning *)

signature TRAVERSER =
sig

  (* type kind *)
  type tp
  type obj

  type head
  type spine

  type dec

  type condec

  val atom : head * spine -> tp
  val arrow : tp * tp -> tp
  val pi : dec * tp -> tp

  val root : head * spine * tp -> obj (* propagate type to every root *)
  val lam : dec * obj -> obj

  val bvar : string -> head
  val const : string list * string -> head
  val def : string list * string -> head 
  (* no evar, skonst, or fvar *)

  val nils : spine
  val app : obj * spine -> spine

  val dec : string * tp -> dec

  val objdec : string * tp -> condec
  (* val famdec : string * kind -> condec *)
  (* val objdef : string * obj * tp -> condec *)
  (* val famdef : string * tp * kind -> condec *)
  (* val skodec : string * tp -> condec *)

end;  (* signature TRAVERSER *)

signature TRAVERSE =
sig

  (*! structure IntSyn : INTSYN !*)
  structure Traverser : TRAVERSER

  exception Error of string

  val fromConDec : IntSyn.ConDec -> Traverser.condec option

  val const : string -> Traverser.condec

end;  (* signature TRAVERSE *)
