(* Diophantine Equation Solver *)
(* Author: Roberto Virga *)

functor CSEqIntegers (structure Integers : INTEGERS
                      structure IntSyn : INTSYN
                      structure Whnf : WHNF
                        sharing Whnf.IntSyn = IntSyn
                      structure Unify : UNIFY
                        sharing Unify.IntSyn = IntSyn
                      structure CSManager : CS_MANAGER
                        sharing CSManager.IntSyn = IntSyn)
 : CS_EQ_INTEGERS =
struct
  structure CSManager = CSManager

  structure Integers = Integers
  structure IntSyn = IntSyn

  type 'a mset = 'a list                 (* MultiSet                   *)

  datatype Sum =                         (* Sum :                      *)
    Sum of Integers.int * Mon mset       (* Sum ::= m + M1 + ...       *)

  and Mon =                              (* Monomials:                 *)
    Mon of Integers.int * (IntSyn.Exp * IntSyn.Sub) mset
                                         (* Mon ::= n * U1[s1] * ...   *)
  local

    open IntSyn
    open Integers

    structure FX = CSManager.Fixity
    structure MS = CSManager.ModeSyn

    val zero = fromInt 0
    val one  = fromInt 1

    val myID = ref ~1 : csid ref

    val numberID = ref ~1 : cid ref

    fun number () = Root (Const (!numberID), Nil)

    val unaryMinusID  = ref ~1 : cid ref
    val plusID        = ref ~1 : cid ref
    val minusID       = ref ~1 : cid ref
    val timesID       = ref ~1 : cid ref

    fun unaryMinusExp (U) = Root (Const (!unaryMinusID), App (U, Nil))
    fun plusExp (U, V)    = Root (Const (!plusID), App (U, App (V, Nil)))
    fun minusExp (U, V)   = Root (Const (!minusID), App (U, App (V, Nil)))
    fun timesExp (U, V)   = Root (Const (!timesID), App (U, App (V, Nil)))

    fun numberConDec (d) = ConDec (toString (d), 0, Normal, number (), Type)
    fun numberExp (d) = Root (FgnConst (!myID, numberConDec (d)), Nil)

    fun parseNumber string =
          (case fromString (string)
             of SOME(d) => SOME(numberConDec (d))
              | NONE => NONE)

    fun solveNumber (G, S, k) = SOME(numberExp (fromInt k))

    fun findMSet eq (x, L) =
          let
            fun findMSet' (tried, nil) = NONE
              | findMSet' (tried, y :: L) =
                  if eq(x, y) then SOME(y, tried @ L)
                  else findMSet' (y :: tried, L)
          in
            findMSet' (nil, L)
          end

    fun equalMSet eq =
          let
              fun equalMSet' (nil, nil) = true
                | equalMSet' (x :: L1', L2) =
                    (case (findMSet eq (x, L2))
                       of SOME (y, L2') => (equalMSet' (L1', L2'))
                        | NONE => false)
                | equalMSet' _ = false
            in
              equalMSet'
            end
      
    fun fromExpW (Us as (FgnExp (cs, ops), _)) =
          if (cs = !myID)
          then recoverSum (#toInternal(ops) ())
          else Sum (zero, [Mon (one, [Us])])
      | fromExpW (Us as (Root (FgnConst (cs, conDec), _), _)) =
          if (cs = !myID)
          then (case (fromString (conDecName (conDec)))
                  of SOME(m) => Sum (m, nil))
          else Sum (zero, [Mon (one, [Us])])
      | fromExpW Us =
          Sum (zero, [Mon (one, [Us])])
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    and recoverSum (U as Root (Const (cid), App (U1, App (U2, Nil)))) =
          if (cid = !plusID)
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
              Sum (zero, [mon])
            end
      | recoverSum (U as Root (FgnConst (cs, conDec), Nil)) =
          if (cs = !myID)
          then
            let
              val SOME(m) = fromString (conDecName (conDec))
            in
              Sum (m, nil)
            end
          else
            Sum (zero, [Mon (one, [(U, id)])])
      | recoverSum U =
          let
            val mon = recoverMon U
          in
            Sum (zero, [mon])
          end
    and recoverMon (U as Root (Const (cid), App (U1, App (U2, Nil)))) =
          if (cid = !timesID)
          then
            let
              val Mon (n, UsL) = recoverMon U1
              val Us = recoverEClo U2
            in
              Mon (n, Us :: UsL)
            end
          else
            Mon (zero, [(U, id)])
      | recoverMon (U as Root (FgnConst (cs, conDec), Nil)) =
          if (cs = !myID)
          then
            let
              val SOME(m) = fromString (conDecName (conDec))
            in
              Mon (m, nil)
            end
          else
            Mon (one, [(U, id)])
      | recoverMon U =
          let
            val Us = recoverEClo U
          in
            Mon (one, [Us])
          end
    and recoverEClo (EClo Us) = Us
      | recoverEClo U = (U, id)

    fun toExp (Sum (m, nil)) = numberExp m
      | toExp (Sum (m, [mon])) =
          if (m = zero) then toExpMon mon
          else plusExp (toExp (Sum (m, nil)), toExpMon mon)
      | toExp (Sum (m, monLL as (mon :: monL))) =
          plusExp (toExp (Sum (m, monL)), toExpMon mon)
    and toExpMon (Mon (n, nil)) = numberExp n
      | toExpMon (Mon (n, [Us])) =
          if (n = one) then toExpEClo Us
          else timesExp (toExpMon (Mon (n, nil)), toExpEClo Us)
      | toExpMon (Mon (n, Us :: UsL)) =
          timesExp (toExpMon (Mon (n, UsL)), toExpEClo Us)
    and toExpEClo (U, Shift (0)) = U
      | toExpEClo Us = EClo Us

    fun compatibleMon (Mon (_, UsL1), Mon (_, UsL2)) =
          equalMSet (fn ((U1, s1), (U2, s2)) => sameExp (U1, U2)
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

    fun plusSum (Sum (m1, nil), Sum (m2, monL2)) =
          Sum (m1 + m2, monL2)
      | plusSum (Sum (m1, monL1), Sum (m2, nil)) =
          Sum (m1 + m2, monL1)
      | plusSum (Sum (m1, mon1 :: monL1), Sum (m2, monL2)) =
          plusSumMon (plusSum (Sum (m1, monL1), Sum (m2, monL2)), mon1)

    and plusSumMon (Sum (m, nil), mon) = Sum (m, [mon])
      | plusSumMon (Sum (m, monL), mon as Mon (n, UsL)) =
          (case (findMSet compatibleMon (mon, monL))
             of SOME (Mon (n', _), monL') =>
                  let
                    val n'' = n + n'
                  in
                    if (n'' = zero) then Sum (m, monL')
                    else Sum (m, (Mon (n'', UsL)) :: monL')
                  end
              | NONE =>
                  Sum (m, mon :: monL))

      fun timesSum (Sum (m1, nil), Sum (m2, nil)) =
          Sum (m1 * m2, nil)
      | timesSum (Sum (m1, mon1 :: monL1), sum2) =
          plusSum (timesSumMon (sum2, mon1), timesSum (Sum (m1, monL1), sum2))
      | timesSum (sum1, Sum (m2, mon2 :: monL2)) =
          plusSum (timesSumMon (sum1, mon2), timesSum (sum1, Sum (m2, monL2)))

    and timesSumMon (Sum (m, nil), Mon (n, UsL)) =
          let
            val n' = m * n
          in
            if (n' = zero) then Sum (n', nil)
            else Sum (zero, [Mon (n', UsL)])
          end
      | timesSumMon (Sum (m, (Mon (n', UsL')) :: monL), mon as Mon (n, UsL)) =
          let
            val n'' = n * n'
            val UsL'' = UsL @ UsL'
            val Sum (m', monL') = timesSumMon (Sum (m, monL), mon)
          in
            Sum (m', (Mon (n'', UsL'')) :: monL')
          end

    fun unaryMinusSum (sum) =
          timesSum (Sum (~one, nil), sum)

    fun minusSum (sum1, sum2) =
          plusSum (sum1, unaryMinusSum (sum2))

    fun normalizeSum (sum as (Sum (m, nil))) = sum
      | normalizeSum (Sum (m, [mon])) =
          plusSum (Sum (m, nil), normalizeMon mon)
      | normalizeSum (Sum (m, mon :: monL)) =
          plusSum (normalizeMon mon, normalizeSum (Sum (m, monL)))
    and normalizeMon (mon as (Mon (n, nil))) = Sum (n, nil)
      | normalizeMon (Mon (n, [Us])) =
          timesSum (Sum (n, nil), fromExp Us)
      | normalizeMon (mon as (Mon (n, Us :: UsL))) =
          timesSum (fromExp Us, normalizeMon (Mon (n, UsL)))

    and mapSum (f, Sum (m, monL)) =
          Sum (m, List.map (fn mon => mapMon (f, mon)) monL)
    and mapMon (f, Mon (n, UsL)) =
          Mon (n, List.map (fn Us => Whnf.whnf (f (EClo Us), id)) UsL)

    fun solvableSum (Sum(m, monL)) =
          let
            fun gcd_list (n1 :: nil) = n1
              | gcd_list (n1 :: n2 :: nil) = gcd(n1, n2)
              | gcd_list (n1 :: n2 :: l) = gcd (gcd (n1, n2), gcd_list l)
            val coeffL = List.map (fn Mon(n, _) => n) monL
            val g = gcd_list coeffL
          in
            rem (m, gcd_list coeffL) = zero
          end

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

    fun divideSum (Sum(m, monL), k) =
          let
            exception Err
            fun divide n = 
                  if rem(n, k) = zero then quot(n, k)
                  else raise Err
            fun divideMon (Mon(n, UsL)) = Mon (divide n, UsL)
          in
            (SOME(Sum(divide m, List.map divideMon monL)))
              handle Err => NONE
          end

    fun delaySum (G, sum) =
          let
            val U = toFgn sum
            val cnstr = ref (Eqn (G, U, numberExp (zero)))
          in
            Delay (U, cnstr)
          end

    and solveSum (G, sum as Sum(m, [Mon(n, [(X as EVar (r, _, _, _), s)])])) =
          if Whnf.isPatSub s
          then [Assign (G, X, numberExp (~(quot(m, n))), Whnf.invert s)]
          else [delaySum (G, sum)]
      | solveSum (G, sum) =
          let
            fun invertMon (G, mon as Mon (n, [(EVar (r, _, _, _), s)]), sum) =
                  if Whnf.isPatSub s
                  then
                    let
                      val ss = Whnf.invert s
                      val RHS = toFgn sum
                    in
                      if Unify.invertible (G, (RHS, id), ss, r)
                      then SOME (mon, ss, sum)
                      else NONE
                    end
                  else NONE
              | invertMon (G, mon, sum) = NONE
          in
            case findMon invertMon (G, sum)
              of SOME (Mon(n1, [(X1, s1)]), ss1, sum1) =>
                   (case findMon invertMon (G, sum1)
                      of SOME (Mon(n2, [(X2, s2)]), ss2, sum2) =>
                           let
                             val s = Unify.intersection (s1, s2)
                             val ss = Whnf.invert s
                             val G' = Whnf.strengthen (ss, G)
                             val g = gcd (n1, n2)
                             val (x1, x2) = solve_gcd (n1, n2)
                             val K = newEVar (G', number())
                             val Z = newEVar (G', number())
                           in
                             Assign (G, X1, toFgn(plusSum (Sum (zero, [Mon(quot(n2, g), [(K, ss)])]),
                                                           timesSum (Sum (x1, nil), 
                                                                     Sum (zero, [Mon (one, [(Z, ss)])])))), ss1) ::
                             Assign (G, X2, toFgn(plusSum (Sum (zero, [Mon(~(quot(n1, g)), [(K, ss)])]),
                                                           timesSum (Sum (x2, nil),
                                                                     Sum (zero, [Mon (one, [(Z, ss)])])))), ss2) ::
                             solveSum (G, plusSum (Sum(zero, [Mon(g, [(Z, ss)])]), sum2))
                           end
                       | NONE => 
                           (case divideSum (sum1, n1)
                              of SOME(sum1') => [Assign (G, X1, toFgn(unaryMinusSum (sum1')), ss1)]
                               | NONE => [delaySum (G, sum)]))
               | NONE => [delaySum (G, sum)]
           end

    and unifySum (G, sum1, sum2) =
          let
            fun invertMon (G, Mon (n, [(LHS as EVar (r, _, _, _), s)]), sum) =
                  if Whnf.isPatSub s
                  then
                    let
                      val ss = Whnf.invert s
                      val RHS = toFgn (timesSum (Sum (~n, nil), sum))
                    in
                      if Unify.invertible (G, (RHS, id), ss, r)
                      then SOME (G, LHS, RHS, ss)
                      else NONE
                    end
                  else NONE
          in
            case minusSum (sum2, sum1)
              of Sum (m, nil) => if (m = zero) then Succeed nil else Fail
               | sum => if (solvableSum sum) then Succeed (solveSum (G, sum))
                        else Fail
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
                                   case minusSum (normalizeSum (sum), fromExp (U2, id))
                                     of Sum(m, nil) => (m = zero)
                                      | _ => false)
                  })

    fun makeFgn (arity, opExp) (S) =
          let
            fun makeParams 0 = Nil
              | makeParams n =
                  App (Root(BVar (n), Nil), makeParams (Int.-(n,1)))
            fun makeLam E 0 = E
              | makeLam E n = 
                  Lam (Dec (NONE, number()), makeLam E (Int.-(n,1)))
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

            numberID := 
              installF (ConDec ("integer", 0,
                                Constraint (!myID, solveNumber),
                                Uni (Type), Kind),
                        NONE, SOME(MS.Mnil));

            unaryMinusID :=
              installF (ConDec ("~", 0,
                                Foreign (!myID, makeFgnUnary unaryMinusSum),
                                arrow (number (), number ()),
                                Type),
                        SOME(FX.Prefix (FX.maxPrec)),
                        NONE);

            plusID :=
              installF (ConDec ("+", 0,
                                Foreign (!myID, makeFgnBinary plusSum),
                                arrow (number (), arrow (number (), number ())),
                                Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        NONE);

            minusID :=
              installF (ConDec ("-", 0,
                                  Foreign (!myID, makeFgnBinary minusSum),
                                  arrow (number (), arrow (number (), number ())),
                                  Type),
                        SOME(FX.Infix (FX.dec (FX.dec FX.maxPrec), FX.Left)),
                        NONE);

            timesID :=
              installF (ConDec ("*", 0,
                                  Foreign (!myID, makeFgnBinary timesSum),
                                  arrow (number (), arrow (number (), number ())),
                                  Type),
                        SOME(FX.Infix (FX.dec FX.maxPrec, FX.Left)),
                        NONE);
            ()
          )
  in
    val solver =
          {
            name = ("equality/integers"),
            keywords = "arithmetic,equality",
            needs = ["Unify"],

            fgnConst = SOME({parse = parseNumber}),

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          }

    val fromExp = fromExp
    val toExp = toExp
    val normalize = normalizeSum

    val compatibleMon = compatibleMon

    val number = number
    
    fun unaryMinus U = toFgn (unaryMinusSum (fromExp (U, id)))
    fun plus (U, V) = toFgn (plusSum (fromExp (U ,id), fromExp (V, id)))
    fun minus (U, V) = toFgn (minusSum (fromExp (U, id), fromExp (V, id)))
    fun times (U, V) = toFgn (timesSum (fromExp (U, id), fromExp (V, id)))

    val constant = numberExp
  end
end  (* functor CSEqIntegers *)
