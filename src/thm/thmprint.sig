(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)

signature THMPRINT =
sig
  structure ThmSyn : THMSYN

  val tDeclToString : ThmSyn.TDecl -> string
  val callpatsToString : ThmSyn.Callpats -> string
end;  (* signature THMPRINT *)
