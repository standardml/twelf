(* Translator from Delphin external syntax to Delphin internal syntax *)
(* Author: Richard Fontana, Carsten Schuermann *)
 
signature TRANS = 
sig
  structure DextSyn : DEXTSYN

  exception Error of string

  val internalizeSig : unit -> unit

  val transFor : (* IntSyn.dctx * *) DextSyn.Form -> Tomega.For
  val transDecs: DextSyn.Decs -> Tomega.Prg 

  val externalizePrg : Tomega.Prg -> Tomega.Prg

(* val transPro : DextSyn.Prog -> Tomega.Prg *) 
 end
