(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)

signature THMPRINT =
sig
  structure ThmSyn : THMSYN

  val tDeclToString : ThmSyn.TDecl -> string
end;  (* signature THMPRINT *)
