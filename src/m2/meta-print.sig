(* Meta printer for proof states *)
(* Author: Carsten Schuermann *)

signature METAPRINT =
sig
  structure MetaSyn : METASYN

  val stateToString  : MetaSyn.State -> string
  val sgnToString    : MetaSyn.Sgn -> string
  val modeToString   : MetaSyn.Mode -> string
  val conDecToString  : IntSyn.ConDec -> string

end; (* signature METAPRINT *)
