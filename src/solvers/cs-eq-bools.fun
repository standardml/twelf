(* Booleans Equation Solver *)
(* Author: Roberto Virga *)

functor CSEqBools (structure IntSyn : INTSYN
                   structure Whnf : WHNF
                     sharing Whnf.IntSyn = IntSyn
                   structure Unify : UNIFY
                     sharing Unify.IntSyn = IntSyn
                   structure CSManager : CS_MANAGER
                     sharing CSManager.IntSyn = IntSyn)
 : CS =
struct
  structure CSManager = CSManager

  structure IntSyn = IntSyn

  type 'a set = 'a list                  (* Set                        *)

  datatype Sum =                         (* Sum :                      *)
    Sum of bool * Mon set                (* Sum ::= m + M1 + ...       *)

  and Mon =                              (* Monomials:                 *)
    Mon of (IntSyn.Exp * IntSyn.Sub) set
                                         (* Mon ::= n * U1[s1] * ...   *)
  local
    open IntSyn

    structure FX = CSManager.Fixity
    structure MS = CSManager.ModeSyn

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

    fun member eq (x, L) =
          List.exists (fn y => eq(x, y)) L

    fun differenceSet eq (L1, L2) =
          let
            val L1' = List.filter (fn x => not (member eq (x, L2))) L1
            val L2' = List.filter (fn x => not (member eq (x, L1))) L2
          in
            L1' @ L2'
          end

    fun equalSet eq (L1, L2) =
          (case differenceSet eq (L1, L2)
             of nil => true
              | (_ :: _) => false)

    fun unionSet eq (L1, L2) =
          let
            val L2' = List.filter (fn x => not (member eq (x, L1))) L2
          in
            L1 @ L2'
          end

    fun fromExpW (Us as (FgnExp (cs, ops), _)) =
          if (cs = !myID)
          then recoverSum (#toInternal(ops) ())
          else Sum (false, [Mon [Us]])
      | fromExpW Us =
          Sum (false, [Mon [Us]])
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    and recoverSum (U as Root (Const (cid), App (U1, App (U2, Nil)))) =
          if (cid = !xorID)
          then
            let
              val Sum (m, monL) = recoverSum U1
              val mon = recoverMon U2
            in
              Sum (m, mon :: monL)
            end
          else 
            let
              val mon = recoverMon U
            in
              Sum (false, [mon])
            end
      | recoverSum (U as Root (Const (cid), Nil)) =
          if (cid = !trueID) orelse (cid = !falseID)
          then
            Sum ((cid = !trueID), nil)
          else
            Sum (false, [Mon [(U, id)]])
      | recoverSum U =
          let
            val mon = recoverMon U
          in
            Sum (false, [mon])
          end
    and recoverMon (U as Root (Const (cid), App (U1, App (U2, Nil)))) =
          if (cid = !andID)
          then
            let
              val Mon UsL = recoverMon U1
              val Us = recoverEClo U2
            in
              Mon (Us :: UsL)
            end
          else
            Mon [(U, id)]
      | recoverMon U =
          let
            val Us = recoverEClo U
          in
            Mon [Us]
          end
    and recoverEClo (EClo Us) = Us
      | recoverEClo U = (U, id)

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
    and toExpMon (Mon [Us]) = toExpEClo Us
      | toExpMon (Mon (Us :: UsL)) =
          andExp (toExpMon (Mon UsL), toExpEClo Us)
    and toExpEClo (U, Shift (0)) = U
      | toExpEClo Us = EClo Us

    fun compatibleMon (Mon UsL1, Mon UsL2) =
          equalSet (fn ((U1, s1), (U2, s2)) => sameExp (U1, U2)
                                               andalso sameSub (s1, s2))
                   (UsL1, UsL2)

    and sameExp (EVar (r1, _, _, _), EVar (r2, _, _, _)) = (r1 = r2)
      | sameExp (Root(BVar (k1), _), Root(BVar (k2), _)) = (k1 = k2)
      | sameExp (_, _) = false

    and sameSub (Shift _, Shift _) = true
      | sameSub (Dot (Idx (k1), s1), Dot (Idx (k2), s2)) =
          (k1 = k2) andalso sameSub (s1, s2)
      | sameSub (s1 as Dot (Idx _, _), Shift (k2)) =
          sameSub (s1, Dot (Idx (Int.+(k2,1)), Shift (Int.+(k2,1))))
      | sameSub (Shift (k1), s2 as Dot (Idx _, _)) =
          sameSub (Dot (Idx (Int.+(k1,1)), Shift (Int.+(k1,1))), s2)
      | sameSub (_, _) = false

    and sameEClo ((U1, s1), (U2, s2)) =
          sameExp (U1, U2) andalso sameSub (s1, s2)

    fun xorSum (Sum (m1, monL1), Sum (m2, monL2)) =
          Sum (not (m1 = m2), differenceSet compatibleMon (monL1, monL2))

    fun andSum (sum1 as Sum (false, nil), sum2) = sum1
      | andSum (sum1, sum2 as Sum (false, nil)) = sum2
      | andSum (sum1 as Sum (true, nil), sum2) = sum2
      | andSum (sum1, sum2 as Sum (true, nil)) = sum1
      | andSum (Sum (m1, mon1 :: monL1), sum2) =
          xorSum (andSumMon (sum2, mon1), andSum (Sum (m1, monL1), sum2))

    and andSumMon (Sum (true, nil), mon) = Sum (false, [mon])
      | andSumMon (sum1 as Sum (false, nil), mon) = sum1
      | andSumMon (Sum (m1, (Mon UsL1) :: monL1), mon2 as Mon UsL2) =
          let
            val UsL = unionSet sameEClo (UsL1, UsL2)
          in
            xorSum (Sum (false, [Mon UsL]),
                    andSumMon (Sum (m1, monL1), mon2))
          end

    fun notSum (Sum (m, monL)) =
          Sum (not m, monL)

    fun orSum (sum1, sum2) =
          xorSum (sum1, xorSum (sum2, andSum (sum1, sum2)))

    fun impliesSum (sum1, sum2) =
          notSum (xorSum (sum1, andSum (sum1, sum2)))

    fun iffSum (sum1, sum2) =
           notSum (xorSum (sum1, sum2))

    fun normalizeSum (sum as (Sum (m, nil))) = sum
      | normalizeSum (Sum (m, [mon])) =
          xorSum (Sum (m, nil), normalizeMon mon)
      | normalizeSum (Sum (m, mon :: monL)) =
          xorSum (normalizeMon mon, normalizeSum (Sum (m, monL)))
    and normalizeMon (Mon [Us]) = fromExp Us
      | normalizeMon (Mon (Us :: UsL)) =
          andSum (fromExp Us, normalizeMon (Mon UsL))

    and mapSum (f, Sum (m, monL)) =
          Sum (m, List.map (fn mon => mapMon (f, mon)) monL)
    and mapMon (f, Mon UsL) =
          Mon (List.map (fn Us => Whnf.whnf (f (EClo Us), id)) UsL)

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

    and toFgn (sum as Sum (m, nil)) = toExp (sum)
      | toFgn (sum as Sum (m, monL)) =
          FgnExp (!myID,
                  {
                    toInternal = (fn () => toExp (normalizeSum (sum))),

                    map = (fn f =>
                              toFgn (normalizeSum (mapSum (f, sum)))),
                    unifyWith = (fn (G, U2) =>
                                   unifySum (G, normalizeSum (sum), fromExp (U2, id))),
                    equalTo = (fn U2 =>
                                   case xorSum (normalizeSum (sum), fromExp (U2, id))
                                     of Sum(m, nil) => (m = false)
                                      | _ => false)
                  })

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

    fun init (cs, installF) =
          (
            myID := cs;

            boolID := 
              installF (ConDec ("bool", 0,
                                Constraint (!myID, solveBool),
                                Uni (Type), Kind),
                        NONE, SOME(MS.Mnil));

            trueID :=
              installF (ConDec ("true", 0,
                                Foreign (!myID, (fn _ => toFgn (Sum(true, nil)))),
                                bool (),
                                Type),
                        NONE, NONE);

            falseID :=
              installF (ConDec ("false", 0,
                                Foreign (!myID, (fn _ => toFgn (Sum(false, nil)))),
                                bool (),
                                Type),
                        NONE, NONE);

            notID :=
              installF (ConDec ("!", 0,
                                Foreign (!myID, makeFgnUnary notSum),
                                arrow (bool (), bool ()),
                                Type),
                        SOME(FX.Prefix (FX.maxPrec)), NONE);

            xorID :=
              installF (ConDec ("||", 0,
                                Foreign (!myID, makeFgnBinary xorSum),
                                arrow (bool (), arrow (bool (), bool ())),
                                Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        NONE);

            andID :=
              installF (ConDec ("&", 0,
                                  Foreign (!myID, makeFgnBinary andSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        NONE);

           orID :=
              installF (ConDec ("|", 0,
                                Foreign (!myID, makeFgnBinary orSum),
                                arrow (bool (), arrow (bool (), bool ())),
                                Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        NONE);

            impliesID :=
              installF (ConDec ("=>", 0,
                                  Foreign (!myID, makeFgnBinary impliesSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        NONE);

            iffID :=
              installF (ConDec ("<=>", 0,
                                  Foreign (!myID, makeFgnBinary iffSum),
                                  arrow (bool (), arrow (bool (), bool ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        NONE);

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
