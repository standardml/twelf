(* Printing of functional proof terms *)
(* Author: Carsten Schuermann *)

signature TOMEGAPRINT =
sig
  (*! structure IntSyn : INTSYN !*)
  (*! structure Tomega : TOMEGA  !*)
  structure Formatter : FORMATTER

  exception Error of string

  val formatFor   : Tomega.Dec IntSyn.Ctx * Tomega.For -> Formatter.format
  val forToString : Tomega.Dec IntSyn.Ctx * Tomega.For -> string
  val formatFun : (string list * Tomega.lemma list) * Tomega.Prg -> Formatter.format
    
  val formatPrg : Tomega.Dec IntSyn.Ctx * Tomega.Prg -> Formatter.format
(*  val formatLemmaDec: FunSyn.LemmaDec -> Formatter.format *)

  val funToString : (string list * Tomega.lemma list) * Tomega.Prg -> string
  (* funToString ((names, projs), P)  = s
     cids is the list of mututal recursive type families.  (could also be names)
     projs are the projection functions used internally,  They must be in the
     same order as names.  The nth name corresponds to the nth projection function
  *)
     
  val evarReset : unit -> unit
  val evarName : string -> Tomega.Prg
  val nameEVar : Tomega.Prg -> string

  val prgToString : Tomega.Dec IntSyn.Ctx * Tomega.Prg -> string
    
  val nameCtx   : Tomega.Dec IntSyn.Ctx -> Tomega.Dec IntSyn.Ctx
  val formatCtx : Tomega.Dec IntSyn.Ctx -> Formatter.format
  val ctxToString : Tomega.Dec IntSyn.Ctx -> string

(*  val lemmaDecToString : FunSyn.LemmaDec -> string *)
end;  (* signature TOMEGAPRINT *)

