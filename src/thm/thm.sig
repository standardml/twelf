(* Theorem Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka, Frank Pfenning *)

signature THM =
sig
  structure ThmSyn : THMSYN
  structure Paths : PATHS

  exception  Error of string

  val installTotal : ThmSyn.TDecl * (Paths.region * Paths.region list)
                     -> ThmSyn.ModeSyn.IntSyn.cid list

  val installTerminates : ThmSyn.TDecl * (Paths.region * Paths.region list) 
                          -> ThmSyn.ModeSyn.IntSyn.cid list
  (* -bp *)
  val installReduces : ThmSyn.RDecl * (Paths.region * Paths.region list) 
                       -> ThmSyn.ModeSyn.IntSyn.cid list 

  val installTabled : ThmSyn.TabledDecl -> unit

end;  (* signature THM *)
