(* External Syntax for meta theorems *)
(* Author: Carsten Schuermann *)

signature THMEXTSYN =
sig
  structure ExtSyn : EXTSYN
  structure Paths : PATHS 

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
  val decl : (decs * (ExtSyn.dec * Paths.region)) -> decs

  val top : Paths.region -> theorem
  val exists : decs * (Paths.region * theorem) -> theorem
  val forall : decs * (Paths.region * theorem) -> theorem
  val forallStar : decs * (Paths.region * theorem) -> theorem
  val forallG : (decs * decs) list * (Paths.region * theorem) -> theorem

  val dec : (string * theorem) -> theoremdec

end;  (* signature THMEXTSYN *)


signature THM_RECON =
sig
  structure ThmSyn : THMSYN
  include THMEXTSYN

  exception Error of string
  val tdeclTotDecl : tdecl -> (ThmSyn.TDecl * (Paths.region * Paths.region list))
  val rdeclTorDecl : rdecl -> (ThmSyn.RDecl * (Paths.region * Paths.region list))
  val theoremToTheorem : theorem -> (ThmSyn.ThDecl * Paths.region)
  val theoremDecToTheoremDec : theoremdec -> (string * ThmSyn.ThDecl) * Paths.region
  val proveToProve : prove -> (ThmSyn.PDecl * (Paths.region * Paths.region list))
  val establishToEstablish : establish -> (ThmSyn.PDecl * (Paths.region * Paths.region list))
  val assertToAssert : assert -> (ThmSyn.Callpats * Paths.region list)
end;  (* signature THM_RECON *)
