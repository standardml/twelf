(* Normalizer for Delphin meta level *)
(* Author: Carsten Schuermann *)

signature NORMALIZE = 
sig
  structure IntSyn : INTSYN
  structure Tomega : TOMEGA

  val normalizeFor : (Tomega.For * Tomega.Sub) -> Tomega.For
  val normalizePrg : (Tomega.Prg * Tomega.Sub) -> Tomega.Prg 
  val normalizeSpine : (Tomega.Spine * Tomega.Sub) -> Tomega.Spine 
  val normalizeSub : Tomega.Sub -> Tomega.Sub 
end
