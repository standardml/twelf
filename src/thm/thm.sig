(* Theorem Declarations *)
(* Author: Carsten Schuermann *)

signature THM =
sig
  structure ThmSyn : THMSYN
  structure Paths : PATHS

  exception  Error of string

  val install : ThmSyn.TDecl * (Paths.region * Paths.region list) 
                -> ThmSyn.ModeSyn.IntSyn.cid list
end;  (* signature THM *)
