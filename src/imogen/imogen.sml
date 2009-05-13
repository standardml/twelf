
structure Imogen :> IMOGEN =
struct

open GeneralExt 
open PP.Ops

structure S = IntSyn
structure P = PreFormula
structure F = Formula
structure N = Names
structure List = ListExt
structure C = TypeCheck
structure T = Term
structure Sym = NameFn(val name = "X")

datatype input = ConDec of S.ConDec

val conDecToExp: S.ConDec -> S.Exp =
 fn S.ConDec(_, _, _, _, e, _) => e
  | _ => raise Impossible 

(* -------------------------------------------------------------------------- *)
(*  Conversion to formulas                                                    *)
(* -------------------------------------------------------------------------- *)

local

   structure FCtx : 
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

   val rec expToTerm: FCtx.t * S.Exp -> P.term =
    fn (ctx, S.Root(head, spine)) => 
       case head of 
          S.Const cid => 
          let
             val f = S.sgnLookup cid
             val f' = S.conDecName f
             val ts = spineToTerms(ctx, spine)
          in 
             P.Fn (f', ts)
          end
        | S.BVar n => P.Var(FCtx.lookup(n-1, ctx))
        | S.FVar (x, _, _) => P.Var x
        | _ => raise Unimplemented 

   and spineToTerms: FCtx.t * S.Spine -> P.term list =
    fn (_, S.Nil) => []
     | (ctx, S.App(exp, spine)) => 
       expToTerm(ctx, exp) :: spineToTerms(ctx, spine)
     | (_, S.SClo _) => raise Impossible 

   val rec expToPreFormula: FCtx.t * S.Exp -> P.formula =
    fn (ctx, exp as S.Root(head, spine)) => 
       let in 
          case head of 
             S.Const cid => 
             let
                val p = S.sgnLookup cid
                val p' = S.conDecName p
                fun unop f = 
                    case spineToFormulas(ctx, spine) of
                       [a] => f a
                     | _ => raise Impossible 
                fun binop f = 
                    case spineToFormulas(ctx, spine) of
                       [a, b] => f(a, b)
                     | _ => raise Impossible 
                fun quant f =
                   let
                      val x = Sym.toString(Sym.new())
                      val ctx = FCtx.extend(x, ctx)
                   in
                      case spineToFormulas(ctx, spine) of
                         [t] => f(x, t)
                       | _ => raise Impossible 
                   end
             in
                case p' of
                   "nd" => 
                   let in 
                      case spine of 
                         S.App(e, S.Nil) => expToPreFormula(ctx, e)
                       | _ => raise Impossible 
                   end
                 | "/\\" => binop P.And
                 | "\\/" => binop P.Or
                 | "=>" => binop P.Imp
                 | "true" => P.Top
                 | "false" => P.Bot
                 | "!" => quant P.All
                 | "?" => quant P.Ex
                 | _ => 
                   let
                      val ts = spineToTerms(ctx, spine)
                   in
                      P.Atom(p', Util.Neg, ts)
                   end
             end
           | S.Def cid => 
             let
                val p = S.sgnLookup cid
                val p' = S.conDecName p
                fun unop f = 
                    case spineToFormulas(ctx, spine) of
                       [a] => f a
                     | _ => raise Impossible 
                fun binop f = 
                    case spineToFormulas(ctx, spine) of
                       [a, b] => f(a, b)
                     | _ => raise Impossible 
             in
                case p' of
                   "~" => unop P.Not
                 | "<=>" => binop P.Iff
                 | _ => 
                   let
                      val ts = spineToTerms(ctx, spine)
                   in
                      P.Atom(p', Util.Neg, ts)
                   end
             end
           | _ => 
             let in 
                PP.pp(%[$"Can't translate: ", $(Print.expToString(S.Null, exp))])
              ; raise Impossible 
             end
       end
     | (ctx, exp as S.Lam(S.Dec(_, exp1), exp2)) => 
       let in 
          expToPreFormula(ctx, exp2)
       end
     | (ctx, exp) => 
       let in 
          PP.pp(%[$"Can't translate: ", $(Print.expToString(S.Null, exp))])
        ; raise Impossible 
       end

   and spineToFormulas: FCtx.t * S.Spine -> P.formula list =
    fn (_, S.Nil) => []
     | (ctx, S.App(exp, spine)) => 
       expToPreFormula(ctx, exp) :: spineToFormulas(ctx, spine)
     | (_, S.SClo _) => raise Impossible 

in

val expToFormula: S.Exp -> Formula.formula =
 fn e => P.formula(expToPreFormula(FCtx.empty, e))

end (* local *)

(* -------------------------------------------------------------------------- *)
(*  Solve                                                                     *)
(* -------------------------------------------------------------------------- *)

structure I = FolInstance
structure O = I.Output

val solve: PFormula.neg -> ND.nd option =
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

local

   structure PCtx : 
                sig
                   type t
                   val empty: t
                   val lookup: Label.t * t -> int * F.formula
                   val extend: (Label.t * F.formula) * t -> t
                   val extendV: Var.t * t -> t
                   val lookupV: Var.t * t -> int
                end =
      struct 
         datatype entry = Lab of Label.t * F.formula
                        | Var of Var.t
         type t = entry list
         val empty = []
         fun extend (lf, ctx) = Lab lf :: ctx
         fun extendV (x, ctx) = Var x :: ctx
         fun lookup (x, l) = 
             case List.getIndex (fn Lab (x', _) => Label.eq(x, x') | _ => false) l of
                NONE => raise Impossible 
              | SOME (k, Lab(_, f)) => (k, f)
              | SOME _ => raise Impossible 
         fun lookupV (x, l) = 
             case List.index (fn Var x' => Var.eq(x, x') | _ => false) l of
                NONE => raise Impossible 
              | SOME k => k
      end

   val rec normalizeForm: F.formula -> F.formula =
    fn F.Not a => F.Imp(a, F.Bot)
     | F.And(a1, a2) => F.And(normalizeForm a1, normalizeForm a2)
     | F.Or(a1, a2) => F.Or(normalizeForm a1, normalizeForm a2)
     | F.Imp(a1, a2) => F.Imp(normalizeForm a1, normalizeForm a2)
     | F.Iff(a1, a2) => 
       let
          val a1 = normalizeForm a1
          val a2 = normalizeForm a2
       in
          F.And(F.Imp(a1, a2), F.Imp(a2, a1))
       end
     | F.All(x, a) => F.All(x, normalizeForm a)
     | F.Ex(x, a) => F.Ex(x, normalizeForm a)
     | fm => fm

   val ctxFromList: S.Dec list -> S.Dec S.Ctx =
    fn decs => foldr (Fun.swap S.Decl) S.Null (rev decs)

   val spineFromList: S.Exp list -> S.Spine =
       foldr S.App S.Nil

   val mkExp: S.Head * S.Exp list -> S.Exp =
    fn (e, ts) => S.Root(e, spineFromList ts)

   val lookupCid: string -> S.Head =
    fn s => case N.constLookup(N.Qid([], s)) of
               NONE => raise Impossible 
             | SOME cid => S.Const cid

   val rec termToExp: PCtx.t * T.term -> S.Exp =
    fn (ctx, T.Var x) => mkExp(S.BVar(PCtx.lookupV(x, ctx) + 1), [])
     | (_, T.Param _) => raise Impossible 
     | (ctx, T.Fn(f, ts)) => 
       let
          val f = lookupCid(Func.toString f)
          val ts = map (fn t => termToExp(ctx, t)) ts
       in
          mkExp(f, ts)
       end

   val rec formulaToExp: PCtx.t * F.formula -> S.Exp =
    fn (ctx, F.Atom rel) => 
       let
          val (p, ts) = Rel.dest rel
          val p = lookupCid (Prop.toString p)
          val ts = map (fn t => termToExp(ctx, t)) ts
       in 
          mkExp(p, ts)
       end
     | (_, F.Top) => mkExp(lookupCid "true", [])
     | (_, F.Bot) => mkExp(lookupCid "false", [])
     | (ctx, F.And(a1, a2)) => binop("/\\", ctx, a1, a2)
     | (ctx, F.Or(a1, a2)) => binop("\\/", ctx, a1, a2)
     | (ctx, F.Imp(a1, a2)) => binop("=>", ctx, a1, a2)
     | (ctx, F.Not a) => unop("~", ctx, a)
     | (ctx, F.All xa) => quant("!", ctx, xa)
     | (ctx, F.Ex xa) => quant("?", ctx, xa)
     | (_, fm) => 
       let in 
          PP.pp(%[$"Can't translate: ", F.pp fm])
        ; raise Impossible 
       end

   and binop = 
    fn (f, ctx, a1, a2) => 
       mkExp(lookupCid f, [formulaToExp(ctx, a1), formulaToExp(ctx, a2)])

   and unop = 
    fn (f, ctx, a) => 
       mkExp(lookupCid f, [formulaToExp(ctx, a)])

   and quant = 
    fn (f, ctx, (x, a)) => 
       let
          val i = lookupCid "i"
          val dec = S.Dec(SOME (Var.toString x), mkExp(i, []))
          val ctx = PCtx.extendV(x, ctx)
          val lam = S.Lam(dec, formulaToExp(ctx, a))
       in
          mkExp(lookupCid f, [lam])
       end

   val rec spineToExps: S.Spine -> S.Exp list =
    fn S.Nil => []
     | S.App(e, s) => e :: spineToExps s

   (* Check a proof against a formula while creating the proofterm. *)

   val rec checkIntro: PCtx.t * ND.intro * F.formula -> S.Exp =
    fn (ctx, ND.Pair(t1, t2), F.And(a1, a2)) => 
       let
          val a1' = formulaToExp(ctx, a1)
          val _ = printl ("a1: " ^ Print.expToString(S.Null, a1'))
          val a2' = formulaToExp(ctx, a2)
          val _ = printl ("a2: " ^ Print.expToString(S.Null, a2'))
          val t1' = checkIntro(ctx, t1, a1)
          val t2' = checkIntro(ctx, t2, a2)
          val pair = lookupCid "pair"
       in
          mkExp(pair, [a1', a2', t1', t2'])
       end
     | (ctx, ND.Lam(x, t), F.Imp(a1, a2)) =>
       let
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
          val _ = printl ("a1: " ^ Print.expToString(S.Null, a1'))
          val nd = lookupCid "nd"
          val dec = S.Dec(SOME (Label.toString x), mkExp(nd, [a1']))
          val exp = checkIntro(PCtx.extend((x, a1), ctx), t, a2)
          val lam = lookupCid "lam"
          val tlam = S.Lam(dec, exp)
       in
          mkExp(lam, [a1', a2', tlam])
       end
     | (ctx, ND.Unit, F.Top) => mkExp(lookupCid "unit", [])
     | (ctx, ND.Elim elim, f) => fst(synthElim(ctx, elim))
     | (ctx, ND.Inl t, F.Or(a1, a2)) => 
       let
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
          val t' = checkIntro(ctx, t, a1)
          val inl = lookupCid "inl"
       in
          mkExp(inl, [a1', a2', t'])
       end
     | (ctx, ND.Inr t, F.Or(a1, a2)) => 
       let
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
          val t' = checkIntro(ctx, t, a2)
          val inr = lookupCid "inr"
       in
          mkExp(inr, [a2', a1', t'])
       end
     | (ctx, ND.Case(e, (x1, t1), (x2, t2)), c) =>
       let
          val (e', F.Or(a1, a2)) = synthElim(ctx, e)
          val nd = lookupCid "nd"
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
          val c' = formulaToExp(ctx, c)
          val t1' = checkIntro(PCtx.extend((x1, a1), ctx), t1, c)
          val t2' = checkIntro(PCtx.extend((x2, a2), ctx), t2, c)
          val t1'' = S.Lam(S.Dec(SOME (Label.toString x1), mkExp(nd, [a1'])), t1')
          val t2'' = S.Lam(S.Dec(SOME (Label.toString x2), mkExp(nd, [a2'])), t2')
       in
          mkExp(lookupCid "case", [a1', a2', c', e', t1'', t2''])
       end
     | (ctx, ND.Abort e, a) => 
       let
          val (e, F.Bot) = synthElim(ctx, e)
          val abort = lookupCid "abort"
          val a' = formulaToExp(ctx, a)
       in
          mkExp(abort, [a', e])
       end
     | (ctx, ND.QLam(x, t), a as F.All(x', b)) => 
       let
          val a = formulaToExp(ctx, a)
          val f = case a of 
                     S.Root(_, spine) => 
                     let in 
                        case spineToExps spine of
                           [f] => f
                         | _ => raise Impossible 
                     end
                   | _ => raise Impossible 
          val x'' = Var.new()
          val t' = ND.subst (Term.Var x'', x) t
          val b' = F.subst (Term.Var x'', x') b
          val ctx = PCtx.extendV(x'', ctx)
          val t'' = checkIntro(ctx, t', b')
          val i = lookupCid "i"
          val dec = S.Dec(SOME (Var.toString x''), mkExp(i, []))
          val t = S.Lam(dec, t'')
       in
          mkExp(lookupCid "qlam", [f, t])
       end
     | (_, nd, f) =>
       let in
          PP.pp(%[$"Can't translate: ", &[ ND.pp nd
                                         , F.pp f
                                         ]
               ])
        ; raise Impossible
       end

   (* Construct the proofterm and synthesize the type *)

   and synthElim: PCtx.t * ND.elim -> S.Exp * F.formula =
    fn (ctx, ND.Label l) =>
       let
          val (n, f) = PCtx.lookup(l, ctx)
       in 
          printl ("n: " ^ Int.toString n)
        ; (mkExp(S.BVar (n+1), []), f)
       end
     | (ctx, ND.Fst e) =>
       let
          val fst = lookupCid "fst"
          val (e, F.And(a1, a2)) = synthElim(ctx, e)
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
       in
          (mkExp(fst, [a1', a2', e]), a1)
       end
     | (ctx, ND.Snd e) =>
       let
          val snd = lookupCid "snd"
          val (e, F.And(a1, a2)) = synthElim(ctx, e)
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
       in
          (mkExp(snd, [a1', a2', e]), a2)
       end
     | (ctx, ND.App(e, i)) =>
       let
          val app = lookupCid "app"
          val (e, F.Imp(a1, a2)) = synthElim(ctx, e)
          val a1' = formulaToExp(ctx, a1)
          val a2' = formulaToExp(ctx, a2)
          val i = checkIntro(ctx, i, a1)
       in
          (mkExp(app, [a1', a2', e, i]), a2)
       end
     | (ctx, ND.QApp(e, t)) =>
       let
          val app = lookupCid "qapp"
          val i = lookupCid "i"
          val (e, F.All(x, a)) = synthElim(ctx, e)
          val ctx = PCtx.extendV(x, ctx)
          val a' = formulaToExp(ctx, a)
          val dec = S.Dec(SOME (Var.toString x), mkExp(i,[]))
          val a'' = S.Lam(dec, a')
          val t' = termToExp(ctx, t)
          val tau = F.subst(t, x) a
       in
          (mkExp(app, [a'', e, t']), tau)
       end

in

val ndToExp: ND.nd * F.formula -> S.Exp =
 fn (nd, a) => checkIntro(PCtx.empty, nd, normalizeForm a)

end (* local *)

(* -------------------------------------------------------------------------- *)
(*  Top                                                                       *)
(* -------------------------------------------------------------------------- *)

val doit: input -> unit = 
 fn ConDec dec => 
    let
       val exp = conDecToExp dec 
       val form = expToFormula exp
       val pform = PFormula.formulate form
    in
       case solve pform of
          NONE => printl "Formula is not provable!"
        | SOME nd => 
          let
             val _ = printl "Solution found!"
             val _ = printl "Translating Imogen natural deduction proofterm..."
             val _ = PP.pp (&[ $"Checking proofterm..."
                             , ND.pp nd
                             , ~
                             , $"Against formula..."
                             , $(Print.expToString(S.Null, exp))
                           ])
             val e = ndToExp(nd, form)
          in
             printl "Double checking term with Twelf"
           ; printl (Print.expToString(S.Null, e))
           ; C.check(e, exp)
           ; printl "Proofterm checked!"
          end
    end                             

end
