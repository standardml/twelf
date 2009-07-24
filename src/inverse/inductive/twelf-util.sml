
structure TwelfUtil :> TWELF_UTIL =
struct 

structure List = ListExt
structure S = IntSyn
structure F = Formula
structure T = Term
structure MS = ModeSyn
structure MT = ModeTable
structure P = Print

open GeneralExt 
open PP.Ops

exception TwelfUtil of string

(* -------------------------------------------------------------------------- *)
(*  Util                                                                      *)
(* -------------------------------------------------------------------------- *)

val modeToString : S.Mode -> string =
 fn S.Plus => "+"
  | S.Minus => "-"
  | _ => raise Unimplemented 

val rec mspineToString : S.ModeSpine -> string =
 fn S.Mnil => "[]"
  | S.Mapp(Marg(m, _), t) => modeToString m ^ " :: " ^ mspineToString t

(* -------------------------------------------------------------------------- *)
(*  Cids                                                                      *)
(* -------------------------------------------------------------------------- *)

(* getCons cid
   Get all decs that are constructors of type cid *) 
val getCons : S.cid -> S.ConDec list =
 fn id => 
    let
       fun idExp id exp =
           case exp of 
              S.Root(S.Const cid, _) => cid = id
            | S.Pi(_, exp) => idExp id exp
            | _ => false
       fun idConDec id condec =
           case condec of 
              S.ConDec(_, _, _, _, exp, _) => idExp id exp
            | _ => false
       fun idCon id id' = idConDec id (S.sgnLookup id')
       val (numDecs, _) = S.sgnSize()
       val cids = List.filter (idCon id) (List.upto(0, numDecs-1))
    in
       map S.sgnLookup cids
    end

(* The name of a dec *) 
val decName : S.cid -> string = 
 fn id => case S.sgnLookup id of
             S.ConDec(name, _, _, _, _, _) => name
           | _ => raise Unimplemented 

(* -------------------------------------------------------------------------- *)
(*  Environments                                                              *)
(* -------------------------------------------------------------------------- *)

structure Env :>
             sig
                type t
                type var = string
                val empty: t
                val push: var option * S.Dec * t -> t
                val lookup: t * int -> var
                val toDctx: t -> S.dctx
             end =
   struct 
      type var = string 
      type t = (var option * S.Dec) list
      val empty = []
      fun push (x, dec, t) = (x, dec) :: t
      fun lookup (l, n) = 
          case List.nth(l, n-1) of
             (SOME x, _) => x
           | (NONE, _) => raise Impossible 
      fun toDctx [] = S.Null
        | toDctx ((_, dec)::t) = S.Decl(toDctx t, dec)
   end

(* -------------------------------------------------------------------------- *)
(*  Constructors                                                              *)
(* -------------------------------------------------------------------------- *)

local
   open IntSyn
in

val rec expToFormula : Env.t * Exp -> F.formula = 
 fn (env, exp) => 
    case exp of 
       Root(Const cid, spine) => 
       F.Atom(Rel.make(Prop.hashString (decName cid), spineToTerms(env, spine))) 
     | Pi((dec as Dec(SOME x, _), _), exp) => 
       let
          val env' = Env.push(SOME x, dec, env)
       in
          F.All(Var.hashString x, expToFormula(env', exp))
       end
     | Pi((dec as Dec(NONE, exp1), _), exp2) => 
       let
          val env' = Env.push(NONE, dec, env)
       in
          F.Imp(expToFormula(env, exp1), expToFormula(env', exp2))
       end
     | _ => raise Unimplemented 

and expToTerm : Env.t * Exp -> T.term = 
 fn (env, Root(Const cid, spine)) => 
    T.Fn(Func.hashString (decName cid), spineToTerms(env, spine))
  | (env, Root(BVar n, spine)) => T.Var(Var.hashString (Env.lookup(env, n)))
  | _ => raise Unimplemented 

and spineToTerms : Env.t * Spine -> T.term list =
 fn (_, Nil) => []
  | (env, App(exp, spine)) => expToTerm(env, exp) :: spineToTerms(env, spine)
  | _ => raise Unimplemented 

val decToFormula : ConDec -> F.formula =
 fn ConDec(_, _, _, _, exp, _) => expToFormula(Env.empty, exp)
  | _ => raise Unimplemented 

val rec piLength : Exp -> int =
 fn Pi (_, e) => 1 + piLength e
  | Root _ => 0
  | _ => raise Unimplemented 

val newConsts : int -> Term.term list =
 fn n => List.tabulate(n, fn _ => Term.Fn(Func.newNamed "x", []))

val decToTerm : ConDec -> Term.term =
 fn ConDec(f, _, _, _, exp, _) => 
    Term.Fn(Func.hashString f, newConsts (piLength exp))
  | _ => raise Unimplemented 

end (* local *) 

(* -------------------------------------------------------------------------- *)
(*  Goals                                                                     *)
(* -------------------------------------------------------------------------- *)

local
   open ModeSyn
   open IntSyn
in

val getGoalExp : cid -> Exp =
 fn id =>
    case sgnLookup id of
       ConDec(_, _, _, _, exp, _) => exp
     | _ => raise Unimplemented

val rec negativeModeSpine : ModeSpine -> bool =
 fn Mnil => true
  | Mapp(Marg(Minus, _), mspine) => negativeModeSpine mspine
  | _ => false

val expToString : Env.t * Exp -> string =
 fn (env, exp) => Print.expToString (Env.toDctx env, exp)

val rec goalToFormula : Env.t * Exp * ModeSpine -> F.formula =
 fn (env, exp, mspine) => 
    let in 
     printl ("exp   : " ^ expToString(env, exp));
     printl ("mspine: " ^ mspineToString mspine);
       case (exp, mspine) of 
          (* Output variable *)
          (Pi((dec as Dec (SOME x, _), _), exp2), Mapp(Marg(Minus, _), mspine')) =>
          if not(negativeModeSpine mspine) then
             raise TwelfUtil ("Bad mode: " ^ mspineToString mspine)
          else 
             let
                val env' = Env.push(SOME x, dec, env)
             in
                F.Ex(Var.hashString x, goalToFormula(env', exp2, mspine'))
             end
        (* Output clause *)
        | (Pi((dec as Dec (NONE, exp1), _), exp2), Mapp(Marg(Minus, _), mspine)) =>
          let
             val env' = Env.push(NONE, dec, env)
          in
             F.And(expToFormula(env, exp1), goalToFormula (env', exp2, mspine))
          end
        (* Input variable *) 
        | (Pi((dec as Dec(SOME x, _), _), exp2), Mapp(Marg(Plus, _), mode)) =>
          let
             val env' = Env.push(SOME x, dec, env)
          in
             F.All(Var.hashString x, goalToFormula (env', exp2, mode))
          end
        (* Input clause *)
        | (Pi((dec as Dec(NONE, exp1), _), exp2), Mapp(Marg(Plus, _), mode)) =>
          let
             val env' = Env.push(NONE, dec, env)
          in
             F.Imp(expToFormula(env, exp1), goalToFormula (env', exp2, mode))
          end
        | (Uni Type, _) => F.Top
        | _ => let in 
                  printl("Error: " ^ expToString(env, exp))
                ; printl("       " ^ mspineToString mspine)
                ; raise Unimplemented
               end 
    end

val getGoal : cid -> F.formula =
 fn id =>
    case MT.modeLookup id of
       NONE => raise TwelfUtil ("No mode declaration for " ^ decName id)
     | SOME m => goalToFormula(Env.empty, getGoalExp id, m)

end (* local *)

(* -------------------------------------------------------------------------- *)
(*  Unification                                                               *)
(* -------------------------------------------------------------------------- *)

val unifyConcl : F.formula * Rel.t -> Rel.t list option =
 fn (f, r) => 
    let
       val (xs, b) = F.destAll f 
       val (ants, cons) = F.destImp b
       fun mapFn (F.Atom r) = r
         | mapFn _ = raise Fail "Non-atomic ant"
       val ants = map mapFn ants
       val cons = mapFn cons
    in
       case Rel.unify(r, cons) of 
          NONE => NONE 
        | SOME theta => 
          SOME (Rel.apply theta cons :: map (Rel.apply theta) ants)
    end

(* -------------------------------------------------------------------------- *)
(*  Frames                                                                    *)
(* -------------------------------------------------------------------------- *)


type var = Var.t * IntSyn.cid

val ppVar : var -> PP.pp =
 fn (x, id) => %[Var.pp x, $" : ", PP.int id]

type clause = Var.t * Rel.t * IntSyn.cid

val ppClause : clause -> PP.pp =
 fn (x, r, id) => %[Var.pp x, $" : ", PP.int id]

end
