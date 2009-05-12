
structure Imogen :> IMOGEN =
struct

open ImogenUtil

structure S = IntSyn
structure F = PreFormula
structure P = PFormula
structure N = Names
structure List = ListExt

datatype input = ConDec of S.ConDec

val conDecToExp: S.ConDec -> S.Exp =
 fn S.ConDec(_, _, _, _, e, _) => e
  | _ => raise Impossible 

(* -------------------------------------------------------------------------- *)
(*  Conversion to formulas                                                    *)
(* -------------------------------------------------------------------------- *)

structure Ctx : 
             sig
                type t
                val empty: t
                val lookup: int * t -> string
                val extend: string * t -> t
             end =
   struct 
      type t = string list
      val empty = []
      val extend = op::
      fun lookup (0, s :: _) = s
        | lookup (n, _ :: t) = lookup(n-1, t)
   end

val rec expToTerm: Ctx.t * S.Exp -> F.term =
 fn (ctx, S.Root(head, spine)) => 
    case head of 
       S.Const cid => 
       let
          val f = S.sgnLookup cid
          val f' = S.conDecName f
          val ts = spineToTerms(ctx, spine)
       in 
          F.Fn (f', ts)
       end
     | S.BVar n => F.Var(Ctx.lookup(n, ctx))
     | S.FVar (x, _, _) => F.Var x
     | _ => raise Unimplemented 

and spineToTerms: Ctx.t * S.Spine -> F.term list =
 fn (_, S.Nil) => []
  | (ctx, S.App(exp, spine)) => 
    expToTerm(ctx, exp) :: spineToTerms(ctx, spine)
  | (_, S.SClo _) => raise Impossible 

val rec expToPreFormula: Ctx.t * S.Exp -> F.formula =
 fn (ctx, S.Root(head, spine)) => 
    case head of 
       S.Const cid => 
       let
          val p = S.sgnLookup cid
          val p' = S.conDecName p
          fun binop f = 
              case spineToFormulas(ctx, spine) of
                 [a, b] => f(a, b)
               | _ => raise Impossible 
       in
          case p' of
             "nd" => 
             let in 
                case spine of 
                   S.App(e, S.Nil) => expToPreFormula(ctx, e)
                 | _ => raise Impossible 
             end
           | "/\\" => binop F.And
           | "\\/" => binop F.Or
           | "=>" => binop F.Imp
           | "true" => F.Top
           | "false" => F.Bot
           | _ => 
             let
                val ts = spineToTerms(ctx, spine)
             in
                F.Atom(p', Util.Neg, ts)
             end
       end

and spineToFormulas: Ctx.t * S.Spine -> F.formula list =
 fn (_, S.Nil) => []
  | (ctx, S.App(exp, spine)) => 
    expToPreFormula(ctx, exp) :: spineToFormulas(ctx, spine)
  | (_, S.SClo _) => raise Impossible 

val expToFormula: S.Exp -> Formula.formula =
 fn e => F.formula(expToPreFormula(Ctx.empty, e))

val expToPFormula: S.Exp -> P.neg =
    P.formulate o expToFormula

(* -------------------------------------------------------------------------- *)
(*  Solve                                                                     *)
(* -------------------------------------------------------------------------- *)

structure I = FolInstance
structure O = I.Output

val solve: P.neg -> ND.nd option =
 fn a : I.Type.t => 
    let
       val input = { typ = a
                   , strategy = ProverUtil.VarRule
                   , proofterm = true
                   , maxSeconds = 600
                   , verbose = ProverUtil.none
                   , globalize = true
                   , statusInterval = 100
                   , heuristics = I.Heuristics.default
                   , selectionPolicy = DatabaseUtil.ExhaustSeqs
                   , subsumptionPolicy = DatabaseUtil.RecursiveDelete
                   , ruleSubsumption = true
                   , printLength = 100
                   , swapInterval = 4
                   , depthInterval = 4
                   , timer = Timer.startCPUTimer()
                   }
    in
       case I.prove input of
          O.Success (SOME (nd, _), t, stats) => 
          SOME nd
        | O.Saturated _ => NONE 
        | TimeOut => NONE
    end

(* -------------------------------------------------------------------------- *)
(*  Natural deduction to IntSyn Exp                                           *)
(* -------------------------------------------------------------------------- *)

structure Ctx : 
             sig
                type t
                val empty: t
                val lookup: Label.t * t -> int
                val extend: Label.t * t -> t
             end =
   struct 
      type t = Label.t list
      val empty = []
      val extend = op::
      fun lookup (x, l) = 
          case ListExt.index (fn x' => Label.eq(x, x')) l of
             NONE => raise Impossible 
           | SOME k => k
   end

val spineFromList: S.Exp list -> S.Spine =
    foldr S.App S.Nil

val mkExp: S.Head * S.Exp list -> S.Exp =
 fn (e, ts) => S.Root(e, spineFromList ts)

val lookupCid: string -> S.Head =
 fn s => case N.constLookup(N.Qid([], s)) of
            NONE => raise Impossible 
          | SOME cid => S.Const cid

val rec introToExp: Ctx.t * ND.intro * P.neg -> S.Exp =
 fn (ctx, ND.Pair(a, b)) => 
    let
       val a' = introToExp(ctx, a)
       val b' = introToExp(ctx, b)
       val pair = lookupCid "pair"
    in
       mkExp(pair, [a', b'])
    end
  | (ctx, ND.Lam(x, a)) => 
    let
       val i = S.Root(lookupCid "i", S.Nil)
       val lam = lookupCid "lam"
       val dec = S.Dec(SOME (Label.toString x), i)
       val exp = introToExp(Ctx.extend(x, ctx), a)
    in
       mkExp(lam, [S.Lam(dec, exp)])
    end
  | (ctx, ND.Inl a) => 
    let
       val inl = lookupCid "inl"
       val a' = introToExp(ctx, a)
    in
       mkExp(inl, [a'])
    end
  | (ctx, ND.Inr a) => 
    let
       val inr = lookupCid "inr"
       val a' = introToExp(ctx, a)
    in
       mkExp(inr, [a'])
    end
  | (ctx, ND.Case(e, (x, a), (y, b))) => 
    let
       val case' = lookupCid "case"
       val e' = elimToExp(ctx, e)
       val nd = lookupCid "nd"
       val a' = introToExp(Ctx.extend(x, ctx), a)
       val b' = introToExp(Ctx.extend(y, ctx), b)
       val a'' = S.Lam(S.Dec(SOME (Label.toString x), mkExp(nd, [a'])))
       val b'' = S.Lam(S.Dec(SOME (Label.toString y), mkExp(nd, [b'])))
    in
       S.Root(case', spineFromList[e', a'', b''])
    end



and elimToExp: Ctx.t * ND.elim -> S.Exp =
 fn _ => raise Unimplemented 

val ndToExp: ND.nd * P.neg -> S.Exp =
 fn (nd, a) => introToExp(Ctx.empty, nd, a)

end
