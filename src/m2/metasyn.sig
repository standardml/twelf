(* Meta syntax *)
(* Author: Carsten Schuermann *)

signature METASYN =
sig
  (*! structure IntSyn : INTSYN !*)

  datatype Mode =			(* Mode                       *)
    Bot					(* M ::= Bot                  *)
  | Top					(*     | Top                  *)

  datatype Prefix =			(* Prefix P := *)
    Prefix of IntSyn.dctx		(* G   declarations           *)
            * Mode IntSyn.Ctx		(* Mtx modes                  *)
            * int IntSyn.Ctx		(* Btx splitting depths       *)

  datatype State =			(* State S :=                 *)
    State of string			(*             [name]         *)
             * Prefix			(*             G; Mtx; Btx    *)
             * IntSyn.Exp		(*             |- V           *)

  datatype Sgn =			(* Interface signature        *)
    SgnEmpty				(* IS ::= .                   *)
  | ConDec of IntSyn.ConDec * Sgn       (*      | c:V, IS             *)

  val createAtomConst : IntSyn.dctx * IntSyn.Head -> (IntSyn.Exp * IntSyn.eclo)
  val createAtomBVar : IntSyn.dctx * int -> (IntSyn.Exp * IntSyn.eclo)
end; (* signature METASYN *)
