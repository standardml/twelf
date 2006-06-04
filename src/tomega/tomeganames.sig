(* Naming *)
(* Author: Carsten Schuermann *)

signature TOMEGANAMES = 
  sig
    val decName : Tomega.Dec IntSyn.Ctx * Tomega.Dec -> Tomega.Dec
  end