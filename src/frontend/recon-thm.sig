(* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)

signature THMEXTSYN =
sig
  structure ExtSyn : EXTSYN
  (*! structure Paths : PATHS  !*)

  type order
  val varg : (Paths.region * string list) -> order
  val lex : (Paths.region * order list) -> order
  val simul : (Paths.region * order list) -> order

  type callpats
  val callpats : (string * string option list * Paths.region) list -> callpats

  type tdecl
  val tdecl : order * callpats -> tdecl

  (* -bp *)
  type predicate 
  val predicate : (string * Paths.region) -> predicate

  (* -bp *)
  type rdecl
  val rdecl : predicate * order * order * callpats -> rdecl

  type tableddecl
  val tableddecl :  (string * Paths.region) -> tableddecl

  type keepTabledecl
  val keepTabledecl :  (string * Paths.region) -> keepTabledecl

  type prove
  val prove : int * tdecl -> prove

  type establish
  val establish  : int * tdecl -> establish

  type assert
  val assert : callpats -> assert

  type decs
  type theorem
  type theoremdec

  val null : decs
  val decl : (decs * ExtSyn.dec) -> decs

  val top : theorem
  val exists : decs * theorem -> theorem
  val forall : decs * theorem -> theorem
  val forallStar : decs * theorem -> theorem
  val forallG : (decs * decs) list * theorem -> theorem

  val dec : (string * theorem) -> theoremdec

  (* world checker *)
  type wdecl
  val wdecl : (string list * string) list * callpats -> wdecl
(*  val wdecl : (decs * decs) list * callpats -> wdecl *)

end;  (* signature THMEXTSYN *)


signature RECON_THM =
sig
  structure ThmSyn : THMSYN
  include THMEXTSYN

  exception Error of string
  val tdeclTotDecl : tdecl -> (ThmSyn.TDecl * (Paths.region * Paths.region list))
  val rdeclTorDecl : rdecl -> (ThmSyn.RDecl * (Paths.region * Paths.region list))

  val tableddeclTotabledDecl : tableddecl -> (ThmSyn.TabledDecl * Paths.region)
  val keepTabledeclToktDecl : keepTabledecl -> (ThmSyn.KeepTableDecl * Paths.region)


  val theoremToTheorem : theorem -> ThmSyn.ThDecl
  val theoremDecToTheoremDec : theoremdec -> string * ThmSyn.ThDecl
  val proveToProve : prove -> (ThmSyn.PDecl * (Paths.region * Paths.region list))
  val establishToEstablish : establish -> (ThmSyn.PDecl * (Paths.region * Paths.region list))
  val assertToAssert : assert -> (ThmSyn.Callpats * Paths.region list)
  val wdeclTowDecl : wdecl -> (ThmSyn.WDecl * Paths.region list)
end;  (* signature RECON_THM *)
