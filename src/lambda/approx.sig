(* Approximate language for term reconstruction *)
(* Author: Kevin Watkins *)

signature APPROX =
sig

  (*! structure IntSyn : INTSYN !*)

  datatype Uni =
      Level of int (* 1 = type, 2 = kind, 3 = hyperkind, etc. *)
    | Next of Uni
    | LVar of Uni option ref
              
  datatype Exp =
      Uni of Uni
    | Arrow of Exp * Exp 
    | Const of IntSyn.Head (* Const/Def/NSDef *)
    | CVar of Exp option ref
    | Undefined

  val Type : Uni
  val Kind : Uni
  val Hyperkind : Uni

  (* resets names of undetermined type/kind variables chosen for printing *)
  val varReset : unit -> unit

  val newLVar : unit -> Uni
  val newCVar : unit -> Exp

  val whnfUni : Uni -> Uni
  val whnf : Exp -> Exp

  val uniToApx : IntSyn.Uni -> Uni
  val classToApx : IntSyn.Exp -> Exp * Uni
  val exactToApx : IntSyn.Exp * IntSyn.Exp -> Exp * Exp * Uni

  exception Ambiguous
  val apxToUni : Uni -> IntSyn.Uni
  val apxToClass : IntSyn.dctx * Exp * Uni * bool -> IntSyn.Exp
  val apxToExact : IntSyn.dctx * Exp * IntSyn.eclo * bool -> IntSyn.Exp

  exception Unify of string
  val matchUni : Uni * Uni -> unit
  val match : Exp * Exp -> unit

  val makeGroundUni : Uni -> bool

end
