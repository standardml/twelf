(* Printer for Meta Theorems *)
(* Author: Carsten Schuermann *)

signature THMPRINT =
sig
  structure ThmSyn : THMSYN

  val tDeclToString : ThmSyn.TDecl -> string
  val callpatsToString : ThmSyn.Callpats -> string
  val rDeclToString : ThmSyn.RDecl -> string           (* -bp *)
  val ROrderToString: ThmSyn.RedOrder -> string        (* -bp *)
end;  (* signature THMPRINT *)
