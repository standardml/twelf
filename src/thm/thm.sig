(* Theorem Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka, Frank Pfenning *)

signature THM =
sig
  structure ThmSyn : THMSYN
  (*! structure Paths : PATHS !*)

  exception  Error of string

  val installTotal : ThmSyn.TDecl * (Paths.region * Paths.region list)
                     -> IntSyn.cid list
  val uninstallTotal : IntSyn.cid -> bool

  val installTerminates : ThmSyn.TDecl * (Paths.region * Paths.region list) 
                          -> IntSyn.cid list
  val uninstallTerminates : IntSyn.cid -> bool (* true: was declared, false not *)

  val installReduces : ThmSyn.RDecl * (Paths.region * Paths.region list) 
                       -> IntSyn.cid list 
  val uninstallReduces : IntSyn.cid -> bool

  val installTabled : ThmSyn.TabledDecl -> unit
  val installKeepTable : ThmSyn.KeepTableDecl -> unit

end;  (* signature THM *)
