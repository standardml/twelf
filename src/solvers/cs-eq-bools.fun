(* Booleans Equation Solver *)
(* Author: Roberto Virga *)

functor CSEqBools ((*! structure IntSyn : INTSYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn !*)
                     )
 : CS =
struct
  (*! structure CSManager = CSManager !*)

  (*! structure IntSyn = IntSyn !*)

  type 'a set = 'a list                  (* Set                        *)

  datatype Sum =                         (* Sum :                      *)
    Sum of bool * Mon set                (* Sum ::= m + M1 + ...       *)

  and Mon =                              (* Monomials:                 *)
    Mon of (IntSyn.Exp * IntSyn.Sub) set
                                         (* Mon ::= U1[s1] * ...       *)

  (* A monomial (U1[s1] * U2[s2] * ...) is said to be normal iff
       (a) each (Ui,si) is in whnf and not a foreign term corresponding
           to a sum;
       (b) the terms Ui[si] are pairwise distinct.
     A sum is normal iff all its monomials are normal, and moreover they
     are pairwise distinct.
  *)

  local
    open IntSyn

    structure FX = CSManager.Fixity
    structure MS = ModeSyn (* CSManager.ModeSyn *)

    exception MyIntsynRep of Sum

    fun extractSum (MyIntsynRep sum) = sum
      | extractSum fe = raise (UnexpectedFgnExp fe)

    val myID = ref ~1 : csid ref

    val boolID = ref ~1 : cid ref

    fun bool () = Root (Const (!boolID), Nil)

    val trueID  = ref ~1 : cid ref
    val falseID = ref ~1 : cid ref

    fun trueExp ()  = Root (Const (!trueID), Nil)
    fun falseExp () = Root (Const (!falseID), Nil)

    fun solveBool (G, S, 0) = SOME(trueExp ())
      | solveBool (G, S, 1) = SOME(falseExp ())
      | solveBool (G, S, k) = NONE

    val notID     = ref ~1 : cid ref
    val xorID     = ref ~1 : cid ref
    val andID     = ref ~1 : cid ref
    val orID      = ref ~1 : cid ref
    val impliesID = ref ~1 : cid ref
    val iffID     = ref ~1 : cid ref

    fun notExp (U)        = Root (Const (!notID), App (U, Nil))
    fun xorExp (U, V)     = Root (Const (!xorID), App (U, App (V, Nil)))
    fun andExp (U, V)     = Root (Const (!andID), App (U, App (V, Nil)))
    fun orExp (U, V)      = Root (Const (!orID), App (U, App (V, Nil)))
    fun impliesExp (U, V) = Root (Const (!impliesID), App (U, App (V, Nil)))
    fun iffExp (U, V)     = Root (Const (!iffID), App (U, App (V, Nil)))

    (* member eq (x, L) = true iff there there is a y in L s.t. eq(y, x) *)
    fun member eq (x, L) =
          List.exists (fn y => eq(x, y)) L

    (* differenceSet eq L1 L2 = (L1 \ L2) U (L2 \ L1) *)
    fun differenceSet eq (L1, L2) =
          let
            val L1' = List.filter (fn x => not (member eq (x, L2))) L1
            val L2' = List.filter (fn x => not (member eq (x, L1))) L2
          in
            L1' @ L2'
          end

    (* equalSet eq (L1, L2) = true iff L1 is equal to L2 (both seen as sets) *)
    fun equalSet eq (L1, L2) =
          (case differenceSet eq (L1, L2)
             of nil => true
              | (_ :: _) => false)

    (* unionSet eq (L1, L2) = L1 U L2 *)
    fun unionSet eq (L1, L2) =
          let
            val L2' = List.filter (fn x => not (member eq (x, L1))) L2
          in
            L1 @ L2'
          end

    (* toExp sum = U

       Invariant:
       If sum is normal
       G |- U : V and U is the Twelf syntax conversion of sum
    *)
    fun toExp (Sum (m, nil)) =
          let
            val cid = if m then !trueID else !falseID
          in
            Root(Const (cid), Nil)
          end
      | toExp (Sum (m, [mon])) =
          if (m = false) then toExpMon mon
          else xorExp (toExp (Sum (m, nil)), toExpMon mon)
      | toExp (Sum (m, monLL as (mon :: monL))) =
          xorExp (toExp (Sum (m, monL)), toExpMon mon)

    (* toExpMon mon = U

       Invariant:
       If mon is normal
       G |- U : V and U is the Twelf syntax conversion of mon
    *)
    and toExpMon (Mon [Us]) = toExpEClo Us
      | toExpMon (Mon (Us :: UsL)) =
          andExp (toExpMon (Mon UsL), toExpEClo Us)

    (* toExpEClo (U,s) = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of Us
    *)
    and toExpEClo (U, Shift (0)) = U
      | toExpEClo Us = EClo Us

    (* compatibleMon (mon1, mon2) = true only if mon1 = mon2 (as monomials) *)
    fun compatibleMon (Mon UsL1, Mon UsL2) =
          equalSet (fn (Us1, Us2) => sameExp (Us1, Us2))
                   (UsL1, UsL2)

    (* sameExpW ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1    (U1,s1)  in whnf
       and  G |- s2 : G2    G2 |- U2 : V2    (U2,s2)  in whnf
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and sameExpW (Us1 as (Root (H1, S1), s1), Us2 as (Root (H2, S2), s2)) =
          (case (H1, H2) of
             (BVar(k1), BVar(k2)) =>
               (k1 = k2) andalso sameSpine ((S1, s1), (S2, s2))
           | (FVar (n1,_,_), FVar (n2,_,_)) =>
               (n1 = n2) andalso sameSpine ((S1, s1), (S2, s2))
           | _ => false)
      | sameExpW (Us1 as (U1 as EVar(r1, G1, V1, cnstrs1), s1),
                  Us2 as (U2 as EVar(r2, G2, V2, cnstrs2), s2)) =
         (r1 = r2) andalso sameSub (s1, s2)
      | sameExpW _ = false

    (* sameExp ((U1,s1), (U2,s2)) = T

       Invariant:
       If   G |- s1 : G1    G1 |- U1 : V1
       and  G |- s2 : G2    G2 |- U2 : V2
       then T only if U1[s1] = U2[s2] (as expressions)
    *)
    and sameExp (Us1, Us2) = sameExpW (Whnf.whnf Us1, Whnf.whnf Us2)

    (* sameSpine (S1, S2) = T

       Invariant:
       If   G |- S1 : V > W
       and  G |- S2 : V > W
       then T only if S1 = S2 (as spines)
    *)
    and sameSpine ((Nil, s1), (Nil, s2)) = true
      | sameSpine ((SClo (S1, s1'), s1), Ss2) =
          sameSpine ((S1, comp (s1', s1)), Ss2)
      | sameSpine (Ss1, (SClo (S2, s2'), s2)) =
          sameSpine (Ss1, (S2, comp (s2', s2)))
      | sameSpine ((App (U1, S1), s1), (App (U2, S2), s2)) =
          sameExp ((U1, s1), (U2, s2))
            andalso sameSpine ((S1, s1), (S2, s2))
      | sameSpine _ = false

    (* sameSub (s1, s2) = T

       Invariant:
       If   G |- s1 : G'
       and  G |- s2 : G'
       then T only if s1 = s2 (as substitutions)
    *)
    and sameSub (Shift _, Shift _) = true
      | sameSub (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) =
          (k1 = k2) andalso sameSub (s1, s2)
      | sameSub (s1 as Dot (Idx _, _), Shift (k2)) =
          sameSub (s1, Dot (Idx (Int.+(k2,1)), Shift (Int.+(k2,1))))
      | sameSub (Shift (k1), s2 as Dot (Idx _, _)) =
          sameSub (Dot (Idx (Int.+(k1,1)), Shift (Int.+(k1,1))), s2)
      | sameSub _ = false

    (* xorSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 xor sum2
    *)
    fun xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
          Sum (not (m1 = m2), differenceSet compatibleMon (monL1, monL2))

    (* andSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 and sum2
    *)
    fun andSum (sum1 as Sum (false, nil), sum2) = sum1
      | andSum (sum1, sum2 as Sum (false, nil)) = sum2
      | andSum (sum1 as Sum (true, nil), sum2) = sum2
      | andSum (sum1, sum2 as Sum (true, nil)) = sum1
      | andSum (Sum (m1, mon1 :: monL1), sum2) =
          xorSum (andSumMon (sum2, mon1), andSum (Sum (m1, monL1), sum2))

    (* andSumMon (sum1, mon2) = sum3

       Invariant:
       If   sum1 normal
       and  mon2 normal
       then sum3 normal
       and  sum3 = sum1 and mon2
    *)
    and andSumMon (Sum (true, nil), mon) = Sum (false, [mon])
      | andSumMon (sum1 as Sum (false, nil), mon) = sum1
      | andSumMon (Sum (m1, (Mon UsL1) :: monL1), mon2 as Mon UsL2) =
          let
            val UsL = unionSet sameExp (UsL1, UsL2)
          in
            xorSum (Sum (false, [Mon UsL]),
                    andSumMon (Sum (m1, monL1), mon2))
          end

    (* notSum sum = sum'

       Invariant:
       If   sum  normal
       then sum' normal
       and  sum' = not sum
    *)
    fun notSum (Sum (m, monL)) =
          Sum (not m, monL)

    (* orSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 or sum2
    *)
    fun orSum (sum1, sum2) =
          xorSum (sum1, xorSum (sum2, andSum (sum1, sum2)))

    (* impliesSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 implies sum2
    *)
    fun impliesSum (sum1, sum2) =
          notSum (xorSum (sum1, andSum (sum1, sum2)))

    (* iffSum (sum1, sum2) = sum3

       Invariant:
       If   sum1 normal
       and  sum2 normal
       then sum3 normal
       and  sum3 = sum1 iff sum2
    *)
    fun iffSum (sum1, sum2) =
           notSum (xorSum (sum1, sum2))

    (* fromExpW (U, s) = sum

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then sum is the internal representation of U[s] as sum of monomials
       and sum is normal
    *)
    fun fromExpW (Us as (FgnExp (cs, fe), _)) =
          if (cs = !myID)
          then normalizeSum (extractSum fe)
          else Sum (false, [Mon [Us]])
      | fromExpW Us =
          Sum (false, [Mon [Us]])
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    (* normalizeSum sum = sum', where sum' normal and sum' = sum *)
    and normalizeSum (sum as (Sum (m, nil))) = sum
      | normalizeSum (Sum (m, [mon])) =
          xorSum (Sum (m, nil), normalizeMon mon)
      | normalizeSum (Sum (m, mon :: monL)) =
          xorSum (normalizeMon mon, normalizeSum (Sum (m, monL)))

    (* normalizeMon mon = mon', where mon' normal and mon' = mon *)
    and normalizeMon (Mon [Us]) = fromExp Us
      | normalizeMon (Mon (Us :: UsL)) =
          andSum (fromExp Us, normalizeMon (Mon UsL))

    (* mapSum (f, m + M1 + ...) = m + mapMon(f,M1) + ... *)
    and mapSum (f, Sum (m, monL)) =
          Sum (m, List.map (fn mon => mapMon (f, mon)) monL)

    (* mapMon (f, n * (U1,s1) + ...) = n * f(U1,s1) * ... *)
    and mapMon (f, Mon UsL) =
          Mon (List.map (fn Us => Whnf.whnf (f (EClo Us), id)) UsL)

    (* appSum (f, m + M1 + ...) = ()     and appMon (f, Mi) for each i *)
    fun appSum (f, Sum (m, monL)) =
        List.app (fn mon => appMon (f, mon)) monL

    (* appMon (f, n * (U1, s1) + ... ) = () and f (Ui[si]) for each i *)
    and appMon (f, Mon UsL) =
        List.app (fn Us => f (EClo Us)) UsL

    (* findMon f (G, sum) =
         SOME(x) if f(M) = SOME(x) for some monomial M in sum
         NONE    if f(M) = NONE for all monomials M in sum
    *)
    fun findMon f (G, Sum(m, monL)) =
          let
            fun findMon' (nil, monL2) = NONE
              | findMon' (mon :: monL1, monL2) =
                  (case (f (G, mon, Sum(m, monL1 @ monL2)))
                     of (result as SOME _) => result
                      | NONE => findMon' (monL1, mon :: monL2))
          in
            findMon' (monL, nil)
          end

    (* unifySum (G, sum1, sum2) = result

       Invariant:
       If   G |- sum1 : number     sum1 normal
       and  G |- sum2 : number     sum2 normal
       then result is the outcome (of type FgnUnify) of solving the
       equation sum1 = sum2 by gaussian elimination.
    *)
    fun unifySum (G, sum1, sum2) =
          let
            fun invertMon (G, Mon [(LHS as EVar (r, _, _, _), s)], sum) =
                  if Whnf.isPatSub s
                  then
                    let
                      val ss = Whnf.invert s
                      val RHS = toFgn sum
                    in
                      if Unify.invertible (G, (RHS, id), ss, r)
                      then SOME (G, LHS, RHS, ss)
                      else NONE
                    end
                  else NONE
              | invertMon _ = NONE
          in
            case xorSum (sum2, sum1)
              of Sum (false, nil) => Succeed nil
               | Sum (true, nil) => Fail
               | sum =>
                  (
                    case findMon invertMon (G, sum)
                      of SOME assignment =>
                           Succeed [Assign assignment]
                       | NONE =>
                           let
                             val U = toFgn sum
                             val cnstr = ref (Eqn (G, U, falseExp ()))
                           in
                             Succeed [Delay (U, cnstr)]
                           end
                  )
          end

    (* toFgn sum = U

       Invariant:
       If sum normal
       then U is a foreign expression representing sum.
    *)
    and toFgn (sum as Sum (m, nil)) = toExp (sum)
      | toFgn (sum as Sum (m, monL)) = FgnExp (!myID, MyIntsynRep sum)

    (* toInternal (fe) = U

       Invariant:
       if fe is (MyIntsynRep sum) and sum : normal
       then U is the Twelf syntax conversion of sum
    *)
    fun toInternal (MyIntsynRep sum) () = toExp (normalizeSum sum)
      | toInternal fe () = raise (UnexpectedFgnExp fe)

    (* map (fe) f = U'

       Invariant:
       if fe is (MyIntsynRep sum)   sum : normal
       and
         f sum = f (m + mon1 + ... + monN) =
               = m + f (m1 * Us1 * ... * UsM) + ...
               = m + (m1 * (f Us1) * ... * f (UsM))
               = sum'           sum' : normal
       then
         U' is a foreign expression representing sum'
    *)
    fun map (MyIntsynRep sum) f = toFgn (normalizeSum (mapSum (f,sum)))
      | map fe _ = raise (UnexpectedFgnExp fe)

    (* app (fe) f = ()

       Invariant:
       if fe is (MyIntsynRep sum)     sum : normal
       and
          sum = m + mon1 + ... monN
          where moni = mi * Usi1 * ... UsiMi
       then f is applied to each Usij
         (since sum : normal, each Usij is in whnf)
    *)
    fun app (MyIntsynRep sum) f = appSum (f, sum)
      | app fe _ = raise (UnexpectedFgnExp fe)

    fun equalTo (MyIntsynRep sum) U2 =
        (case xorSum (normalizeSum (sum), fromExp (U2, id)) (* AK: redundant normalizeSum ? *)
          of Sum(m, nil) => (m = false)
           | _ => false)
      | equalTo fe _ = raise (UnexpectedFgnExp fe)

    fun unifyWith (MyIntsynRep sum) (G, U2) = unifySum (G, normalizeSum sum, fromExp (U2, id))
      | unifyWith fe _ = raise (UnexpectedFgnExp fe)

    fun installFgnExpOps () = let
        val csid = !myID
        val _ = FgnExpStd.ToInternal.install (csid, toInternal)
        val _ = FgnExpStd.Map.install (csid, map)
        val _ = FgnExpStd.App.install (csid, app)
        val _ = FgnExpStd.UnifyWith.install (csid, unifyWith)
        val _ = FgnExpStd.EqualTo.install (csid, equalTo)
    in
        ()
    end

    fun makeFgn (arity, opExp) (S) =
          let
            fun makeParams 0 = Nil
              | makeParams n =
                  App (Root(BVar (n), Nil), makeParams (Int.-(n,1)))
            fun makeLam E 0 = E
              | makeLam E n =
                  Lam (Dec (NONE, bool()), makeLam E (Int.-(n,1)))
            fun expand ((Nil, s), arity) =
                  (makeParams arity, arity)
              | expand ((App (U, S), s), arity) =
                  let
                    val (S', arity') = expand ((S, s), (Int.-(arity,1)))
                  in
                    (App (EClo (U, comp (s, Shift (arity'))), S'), arity')
                  end
              | expand ((SClo (S, s'), s), arity) =
                  expand ((S, comp (s', s)), arity)
            val (S', arity') = expand ((S, id), arity)
          in
            makeLam (toFgn (opExp S')) arity'
          end

    fun makeFgnUnary opSum =
          makeFgn (1,
            fn (App (U, Nil)) =>
               opSum (fromExp (U, id)))

    fun makeFgnBinary opSum =
          makeFgn (2,
            fn (App (U1, App (U2, Nil))) =>
              opSum (fromExp (U1, id), fromExp (U2, id)))

    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    fun init (cs, installF) =
          (
            myID := cs;

            boolID :=
              installF (ConDec ("bool", NONE, 0,
                                Constraint (!myID, solveBool),
                                Uni (Type), Kind),
                        NONE, [MS.Mnil]);

            trueID :=
              installF (ConDec ("true", NONE, 0,
                                Foreign (!myID, (fn _ => toFgn (Sum(true, nil)))),
                                bool (),
                                Type),
                        NONE, nil);

            falseID :=
              installF (ConDec ("false", NONE, 0,
                                Foreign (!myID, (fn _ => toFgn (Sum(false, nil)))),
                                bool (),
                                Type),
                        NONE, nil);

            notID :=
              installF (ConDec ("!", NONE, 0,
                                Foreign (!myID, makeFgnUnary notSum),
                                arrow (bool (), bool ()),
                                Type),
                        SOME(FX.Prefix (FX.maxPrec)),
                        nil);

            xorID :=
              installF (ConDec ("||", NONE, 0,
                                Foreign (!myID, makeFgnBinary xorSum),
                                arrow (bool (), arrow (bool (), bool ())),
                                Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        nil);

            andID :=
              installF (ConDec ("&", NONE, 0,
                                  Foreign (!myID, makeFgnBinary andSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        nil);

           orID :=
              installF (ConDec ("|", NONE, 0,
                                Foreign (!myID, makeFgnBinary orSum),
                                arrow (bool (), arrow (bool (), bool ())),
                                Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        nil);

            impliesID :=
              installF (ConDec ("=>", NONE, 0,
                                  Foreign (!myID, makeFgnBinary impliesSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        nil);

            iffID :=
              installF (ConDec ("<=>", NONE, 0,
                                  Foreign (!myID, makeFgnBinary iffSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        nil);

            installFgnExpOps () ;

            ()
          )
  in
    val solver =
          {
            name = "equality/booleans",
            keywords = "booleans,equality",
            needs = ["Unify"],

            fgnConst = NONE,

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          }
  end
end  (* functor CSEqBools *)
