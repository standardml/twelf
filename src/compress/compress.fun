functor Compress (structure Global : GLOBAL) =
struct

  structure I = IntSyn
  structure S = Syntax
  structure Sgn = Sgn

  exception Unimp
  exception NoModes (* modes are not appropriate for the given I.ConDec *)

  val debug = ref ~1

  fun sgnReset () = Sgn.clear ()

(* xlate_type : IntSyn.Exp -> Syntax.tp *)
  fun xlate_type (I.Pi ((I.Dec(_, e1), _), e2)) = S.TPi(S.MINUS, xlate_type e1, xlate_type e2)
    | xlate_type (I.Root (I.Const cid, sp)) = S.TRoot(cid, xlate_spine sp)
    | xlate_type (I.Root (I.Def cid, sp)) = S.TRoot(cid, xlate_spine sp) (* assuming cids of consts and defs to be disjoint *)
    | xlate_type (I.Root (I.NSDef cid, sp)) = S.TRoot(cid, xlate_spine sp)  (* ditto *)
    | xlate_type (I.Lam (_, t)) = xlate_type t  (* for type definitions, simply strip off the lambdas and leave
                                                   the variables free*)
  and xlate_spine I.Nil = []
    | xlate_spine (I.App(e, s)) = xlate_spinelt e :: xlate_spine s
  and xlate_spinelt e  = S.Elt(xlate_term e)
  and xlate_term (I.Root (I.Const cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp))
    | xlate_term (I.Root (I.Def cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* assuming cids of consts and defs to be disjoint *)
    | xlate_term (I.Root (I.NSDef cid, sp)) = S.ATerm(S.ARoot(S.Const cid, xlate_spine sp)) (* ditto *)
    | xlate_term (I.Root (I.BVar vid, sp)) = S.ATerm(S.ARoot(S.Var (vid - 1), xlate_spine sp))
    | xlate_term (I.Lam (_, e)) = S.NTerm(S.Lam (xlate_term e))
(* xlate_kind : IntSyn.Exp -> Syntax.knd *)
  fun xlate_kind (I.Pi ((I.Dec(_, e1), _), e2)) = S.KPi(S.MINUS, xlate_type e1, xlate_kind e2)
    | xlate_kind (I.Uni(I.Type)) = S.Type

  local open Syntax in
  (* simple skeletal form of types
     omits all dependencies, type constants *)
  datatype simple_tp = Base | Arrow of simple_tp * simple_tp

  fun simplify_tp (TPi (_, t1, t2)) = Arrow(simplify_tp t1, simplify_tp t2)
    | simplify_tp (TRoot _) = Base
  fun simplify_knd (KPi (_, t1, k2)) = Arrow(simplify_tp t1, simplify_knd k2)
    | simplify_knd (Type) = Base

  (* hereditarily perform some eta-expansions on
     a (term, type, spine, etc.) in a context
    (and if not synthesizing) at a simple type.

    The only type of eta-expansion performed is when we
    encounter
    x . (M_1, M_2, ... M_n)
    for a variable x, and M_1, ..., M_n have fewer lambda abstractions
    than their (skeletal) type would suggest.

    The complication with doing full eta-expansion is that if
    we were to wrap lambda abstractions around terms that occur
    in a synthesizing position, we would need to add ascriptions,
    and thus carry full types around everywhere.

    Fortunately, this weakened form of eta-expansion is all
    we need to reconcile the discrepancy between what twelf
    maintains as an invariant, and full eta-longness. *)
  fun eta_expand_term G (NTerm t) T = NTerm(eta_expand_nterm G t T)
    | eta_expand_term G (ATerm t) T = ATerm(eta_expand_aterm G t)
  and eta_expand_nterm G (Lam t) (Arrow(t1, t2)) = Lam(eta_expand_term (t1::G) t t2)
    | eta_expand_nterm G (NRoot (h,s)) T = NRoot(h, eta_expand_spine G s T)
    | eta_expand_nterm G (Lam t) Base = raise Syntax "Lambda occurred where term of base type expected"
  and eta_expand_aterm G (ARoot (Const n, s)) =
      let
          val stp = simplify_tp(typeOf (Sgn.o_classifier n))
      in
          ARoot(Const n, eta_expand_spine G s stp)
      end
    | eta_expand_aterm G (ARoot (Var n, s)) =
      let
          val stp = List.nth(G, n)
      in
          ARoot(Var n, eta_expand_var_spine G s stp)
      end
    | eta_expand_aterm G (ERoot _) = raise Syntax "invariant violated in eta_expand_aterm"
  and eta_expand_tp G (TRoot(n, s)) =
      let
          val stp = simplify_knd(kindOf (Sgn.o_classifier n))
      in
          TRoot(n, eta_expand_spine G s stp)
      end
    | eta_expand_tp G (TPi(m,a,b)) = TPi(m,eta_expand_tp G a, eta_expand_tp (simplify_tp a::G) b)
  and eta_expand_knd G (Type) = Type
    | eta_expand_knd G (KPi(m,a,b)) = KPi(m,eta_expand_tp G a, eta_expand_knd (simplify_tp a::G) b)
  and eta_expand_spine G [] Base = [] (* this seems risky, but okay as long as the only eta-shortness we find is in variable-headed pattern spines *)
    | eta_expand_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_term G m t1) :: eta_expand_spine G tl t2
    | eta_expand_spine G ((AElt m)::tl) (Arrow(t1, t2)) =
      AElt(eta_expand_aterm G m) :: eta_expand_spine G tl t2
    | eta_expand_spine G ((Ascribe(m,a))::tl) (Arrow(t1, t2)) =
      Ascribe(eta_expand_nterm G m t1, eta_expand_tp G a) :: eta_expand_spine G tl t2
    | eta_expand_spine G (Omit::tl) (Arrow(t1,t2)) =
      Omit :: eta_expand_spine G tl t2
    | eta_expand_spine _ _ _ = raise Syntax "Can't figure out how to eta expand spine"
  (* the behavior here is that we are eta-expanding all of the elements of the spine, not the head of *this* spine *)
  and eta_expand_var_spine G [] _ = [] (* in fact this spine may not be eta-long yet *)
    | eta_expand_var_spine G ((Elt m)::tl) (Arrow(t1, t2)) =
      Elt(eta_expand_immediate (eta_expand_term G m t1, t1)) :: eta_expand_spine G tl t2
    | eta_expand_var_spine _ _ _ = raise Syntax "Can't figure out how to eta expand var-headed spine"
  (* here's where the actual expansion takes place *)
  and eta_expand_immediate (m, Base) = m
    | eta_expand_immediate (NTerm(Lam m), Arrow(t1, t2)) =
      NTerm(Lam(eta_expand_immediate(m, t2)))
    | eta_expand_immediate (m, Arrow(t1, t2)) =
      let
          val variable = eta_expand_immediate(ATerm(ARoot(Var 0, [])), t1)
      in
          NTerm(Lam(eta_expand_immediate(apply_to(shift m, variable), t2)))
      end
  and apply_to (ATerm(ARoot(h, s)), m) = ATerm(ARoot(h, s @ [Elt m]))
    | apply_to (NTerm(NRoot(h, s)), m) = NTerm(NRoot(h, s @ [Elt m]))
    | apply_to _ = raise Syntax "Invariant violated in apply_to"
  end

  val typeOf = S.typeOf
  val kindOf = S.kindOf

  exception Debug of S.spine * S.tp * S.tp
 (* val compress_type : Syntax.tp list -> Syntax.mode list option * Syntax.tp -> Syntax.tp *)
 (* the length of the mode list, if there is one, should correspond to the number of pis in the input type.
    however, as indicated in the XXX comment below, it seems necessary to treat SOME of empty list
    as if it were NONE. This doesn't seem right. *)
  fun compress_type G s = (* if !debug < 0
                          then *) compress_type' G s
                          (* else  (if !debug = 0 then raise Debug(G, s) else ();
                                debug := !debug - 1; compress_type' G s) *)
  and compress_type' G (NONE, S.TPi(_, a, b)) = S.TPi(S.MINUS, compress_type G (NONE, a), compress_type (a::G) (NONE, b))
    | compress_type' G (SOME (m::ms), S.TPi(_, a, b)) = S.TPi(m, compress_type G (NONE, a), compress_type (a::G) (SOME ms, b))
    | compress_type' G (SOME [], S.TRoot(cid, sp)) = S.TRoot(cid, compress_type_spine G (sp,
                                                                                   kindOf(Sgn.o_classifier cid),
                                                                                   kindOf(Sgn.classifier cid)))
    | compress_type' G (NONE, a as S.TRoot _) = compress_type G (SOME [], a)
    | compress_type' G (SOME [], a as S.TPi _) = compress_type G (NONE, a) (* XXX sketchy *)

(* XXX: optimization: don't compute mstar if omit? *)
  and compress_type_spine G ([], w, wstar) = []
    | compress_type_spine G ((S.Elt m)::sp, S.KPi(_, a, v), S.KPi(mode, astar, vstar)) =
      let
          val mstar = compress_term G (m, a)
          val sstar = compress_type_spine G (sp,
                                        S.subst_knd (S.TermDot(m, a, S.Id)) v,
                                        S.subst_knd (S.TermDot(mstar, astar, S.Id)) vstar)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end
  and compress_spine G ([], w, wstar) = []
    | compress_spine G ((S.Elt m)::sp, S.TPi(_, a, v), S.TPi(mode, astar, vstar)) =
      let
          val mstar = compress_term G (m, a)
          val sstar = compress_spine G (sp,
                                        S.subst_tp (S.TermDot(m, a, S.Id)) v,
                                        S.subst_tp (S.TermDot(mstar, astar, S.Id)) vstar)
      in
          case (mode, mstar) of
              (S.OMIT, _) => S.Omit::sstar
            | (S.MINUS, _) => S.Elt mstar::sstar
            | (S.PLUS, S.ATerm t) => S.AElt t::sstar
            | (S.PLUS, S.NTerm t) => S.Ascribe(t, compress_type G (NONE, a))::sstar
      end
  and compress_term G (S.ATerm(S.ARoot(S.Var n, sp)), _) =
      let
          val a = S.ctxLookup(G, n)
          val astar = compress_type G (NONE, a)
      in
          S.ATerm(S.ARoot(S.Var n, compress_spine G (sp, a, astar)))
      end
    | compress_term G (S.ATerm(S.ARoot(S.Const n, sp)), _) =
      let
          val a = typeOf (Sgn.o_classifier n)
          val astar = typeOf (Sgn.classifier n)
          val term_former = case Sgn.get_p n of
                                SOME false => S.NTerm o S.NRoot
                              | _ => S.ATerm o S.ARoot
      in
          term_former(S.Const n, compress_spine G (sp, a, astar))
      end
    | compress_term G (S.NTerm(S.Lam t),S.TPi(_, a, b)) = S.NTerm(S.Lam (compress_term (a::G) (t, b)))

  fun compress_kind G (NONE, S.KPi(_, a, k)) = S.KPi(S.MINUS, compress_type G (NONE, a), compress_kind (a::G) (NONE, k))
    | compress_kind G (SOME (m::ms), S.KPi(_, a, k)) = S.KPi(m, compress_type G (NONE, a), compress_kind (a::G) (SOME ms, k))
    | compress_kind G (SOME [], S.Type) = S.Type
    | compress_kind G (NONE, S.Type) = S.Type


(* compress : cid * IntSyn.ConDec -> ConDec *)
  fun compress (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, a, IntSyn.Type)) =
      let
          val x = xlate_type a
          val x = eta_expand_tp [] x
          val modes = Sgn.get_modes cid
      in
          Sgn.condec(name, compress_type [] (modes, x), x)
      end
    | compress (cid, IntSyn.ConDec (name, NONE, _, IntSyn.Normal, k, IntSyn.Kind)) =
      let
          val x = xlate_kind k
          val modes = Sgn.get_modes cid
      in
          Sgn.tycondec(name, compress_kind [] (modes, x), x)
      end
    | compress (cid, IntSyn.ConDef (name, NONE, _, m, a, IntSyn.Type, _)) =
      let
          val m = xlate_term m
          val a = xlate_type a
          val astar = compress_type [] (NONE, a)
          val mstar = compress_term [] (m, a)
      in
          Sgn.defn(name, astar, a, mstar, m)
      end
    | compress (cid, IntSyn.ConDef (name, NONE, _, a, k, IntSyn.Kind, _)) =
      let
          val a = xlate_type a
          val k = xlate_kind k
          val kstar = compress_kind  [] (NONE, k)
          val astar = compress_type (Syntax.explodeKind kstar) (NONE, a)
      in
          Sgn.tydefn(name, kstar, k, astar, a)
      end
    | compress (cid, IntSyn.AbbrevDef (name, NONE, _, m, a, IntSyn.Type)) =
      let
          val m = xlate_term m
          val a = xlate_type a
          val astar = compress_type [] (NONE, a)
          val mstar = compress_term [] (m, a)
      in
          Sgn.abbrev(name, astar, a, mstar, m)
      end
    | compress (cid, IntSyn.AbbrevDef (name, NONE, _, a, k, IntSyn.Kind)) =
      let
          val a = xlate_type a
          val k = xlate_kind k
          val kstar = compress_kind  [] (NONE, k)
          val astar = compress_type (Syntax.explodeKind kstar) (NONE, a)
      in
          Sgn.tyabbrev(name, kstar, k, astar, a)
      end
    | compress _ = raise Unimp

  fun sgnLookup (cid) =
      let
          val c = Sgn.sub cid
      in
          case c of NONE =>
                    let
                        val c' = compress (cid, I.sgnLookup cid)
                        val _ = Sgn.update (cid, c')
                        val _ = print (Int.toString cid ^ "\n")
                    in
                        c'
                    end
                  | SOME x => x
      end

 (*  val sgnApp  = IntSyn.sgnApp

  fun sgnCompress () = sgnApp (ignore o sgnLookup) *)

  fun sgnCompressUpTo x = if x < 0 then () else (sgnCompressUpTo (x - 1); sgnLookup x; ())

  val check = Reductio.check

  fun extract f = ((f(); raise Match) handle Debug x => x)

  val set_modes = Sgn.set_modes

(* val log : Sgn.sigent list ref = ref [] *)


  (* given a cid, pick some vaguely plausible omission modes *)
  fun naiveModes cid =
      let
          val (ak, omitted_args, uni) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a, uni)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a, uni)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a, uni)
                | _ => raise NoModes
          fun count_args (I.Pi(_, ak')) = 1 + count_args ak'
            | count_args _ = 0
          val total_args = count_args ak

          fun can_omit ms =
              let
                  val _ = Sgn.set_modes (cid, ms)
                  val s = compress (cid, I.sgnLookup cid)
                  val t = Sgn.typeOfSigent s
(*                val _ = if true then log := !log @ [s] else () *)
                  val isValid = Reductio.check_plusconst_strictness t
(*                val _ = if isValid then print "yup\n" else print "nope\n" *)
              in
                  isValid
              end

          fun optimize' ms [] = rev ms
            | optimize' ms (S.PLUS::ms') = if can_omit ((rev ms) @ (S.MINUS ::ms'))
                                           then optimize' (S.MINUS::ms) ms'
                                           else optimize' (S.PLUS::ms) ms'
            | optimize' ms (S.MINUS::ms') = if  can_omit ((rev ms) @ (S.OMIT :: ms'))
                                           then optimize' (S.OMIT::ms) ms'
                                           else optimize' (S.MINUS::ms) ms'
          fun optimize ms = optimize' [] ms
      in
          if uni = I.Kind
          then List.tabulate (total_args, (fn _ => S.MINUS))
          else optimize (List.tabulate (total_args, (fn x => if x < omitted_args then S.MINUS else S.PLUS)))
      end


  (* Given a cid, return the "ideal" modes specified by twelf-
     omitted arguments. It is cheating to really use these for
     compression: the resulting signature will not typecheck. *)
  fun idealModes cid =
      let
          val (ak, omitted_args) =
              case I.sgnLookup cid of
                  I.ConDec(name, package, o_a, status, ak, uni) => (ak, o_a)
                | I.ConDef(name, package, o_a, ak, def, uni, _) => (ak, o_a)
                | I.AbbrevDef(name, package, o_a, ak, def, uni) => (ak, o_a)
                | _ => raise NoModes
          fun count_args (I.Pi(_, ak')) = 1 + count_args ak'
            | count_args _ = 0
          val total_args = count_args ak
      in
          List.tabulate (total_args, (fn x => if x < omitted_args then S.OMIT else S.MINUS))
      end

(* not likely to work if the mode-setting function f actually depends on
   properties of earlier sgn entries *)
  fun setModesUpTo x f = if x < 0 then () else (setModesUpTo (x - 1) f;
                                                Sgn.set_modes (x, f x); ())

  fun sgnAutoCompress n f = (let
      val modes = f n
  in
      Sgn.set_modes(n, modes);
      Sgn.update (n, compress (n, IntSyn.sgnLookup n))
  end handle NoModes => ())

  fun sgnAutoCompressUpTo' n0 n f =
      if n0 > n
      then ()
      else let
              val _ =
                 (* has this entry already been processed? *)
                  case Sgn.sub n0
                   of SOME _ => ()
                    (* if not, compress it *)
                    | NONE =>
                      let
                          val modes = f n0
                      in
                           (Sgn.set_modes(n0, modes);
                           Sgn.update (n0, compress (n0, IntSyn.sgnLookup n0));
                           if n0 mod 100 = 0 then print (Int.toString n0 ^ "\n") else ())
                      end handle NoModes => ()
          in
              sgnAutoCompressUpTo' (n0 + 1) n f
          end
  fun sgnAutoCompressUpTo n f = sgnAutoCompressUpTo' 0 n f

  val check = Reductio.check

end

(*
c : ((o -> o) -> o -> o) -> o

a : o -> o

c ([x] a)

eta_expand_immediate ( a) ( o -> o)
*)
