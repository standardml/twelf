(* Solver for machine integers *)
(* Author: Roberto Virga *)

functor CSIntWord ((*! structure IntSyn : INTSYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = IntSyn !*)
                   structure Unify : UNIFY
                   (*! sharing Unify.IntSyn = IntSyn !*)
                   (*! structure CSManager : CS_MANAGER !*)
                   (*! sharing CSManager.IntSyn = IntSyn !*)
                   val wordSize : int)
 : CS =
struct
  (*! structure CSManager = CSManager !*)

  local
    open IntSyn

    structure W = LargeWord;

    structure FX = CSManager.Fixity
    structure MS = ModeSyn (* CSManager.ModeSyn *)

    exception MyFgnCnstrRepPlus of dctx * Exp * Exp * Exp * Exp
                                        (* FgnCnstr Representation: (G, proof, U1, U2, U3) *)
    exception MyFgnCnstrRepTimes of dctx * Exp * Exp * Exp * Exp
    exception MyFgnCnstrRepQuot of dctx * Exp * Exp * Exp * Exp

    val wordSize' = Int.min (wordSize, W.wordSize);

    val zero = W.fromInt 0
    val max = W.>> (W.notb zero, Word.fromInt (W.wordSize - wordSize'))

    (* numCheck (d) = true iff d <= max *)
    fun numCheck (d) = W.<= (d, max)

    (* plusCheck (d1, d2) = true iff d1 + d2 <= max *)
    fun plusCheck (d1, d2) =
          let
            val d3 = W.+ (d1, d2)
          in
            W.>= (d3, d1)
            andalso W.>= (d3, d2)
            andalso W.<= (d3, max)
          end

    (* timesCheck (d1, d2) = true iff d1 * d2 <= max *)
    fun timesCheck (d1, d2) =
          if(d1 = zero orelse d2 = zero) then true
          else let val d3 = W.div (W.div (max, d1), d2)
               in W.> (d3, zero) end

    (* quotCheck (d1, d2) = true iff  d2 != zero *)
    fun quotCheck (d1, d2) = W.> (d2, zero)

    (* constraint solver ID of this module *)
    val myID = ref ~1 : csid ref

    (* constant ID of the type family constant "wordXX" *)
    val wordID = ref ~1 : cid ref

    fun word () = Root (Const (!wordID), Nil)

    (* constant ID's of the operators defined by this module *)
    val plusID  = ref ~1 : cid ref   (* + : wordXX -> wordXX -> wordXX -> type *)
    val timesID = ref ~1 : cid ref   (* * : wordXX -> wordXX -> wordXX -> type *)
    val quotID  = ref ~1 : cid ref   (* / : wordXX -> wordXX -> wordXX -> type *)

    fun plusExp (U, V, W) = Root (Const (!plusID),
                                  App (U, App (V, App (W , Nil))))

    fun timesExp (U, V, W) = Root (Const (!timesID),
                                   App (U, App (V, App (W, Nil))))

    fun quotExp (U, V, W) = Root (Const (!quotID),
                                  App (U, App (V, App (W , Nil))))

    (* constant ID's of the proof object generators and their proof objects *)
    (* (these are used as workaround for the lack of sigma types in Twelf)  *)
    val provePlusID  = ref ~1 : cid ref (* prove+ : {U}{V}{W} + U V W -> type *)
    val proveTimesID = ref ~1 : cid ref (* prove* : {U}{V}{W} * U V W -> type *)
    val proveQuotID  = ref ~1 : cid ref (* prove/ : {U}{V}{W} / U V W -> type *)
    val proofPlusID  = ref ~1 : cid ref (* proof* : {U}{V}{W}{P} prove+ U V W P *)
    val proofTimesID = ref ~1 : cid ref (* proof* : {U}{V}{W}{P} prove* U V W P *)
    val proofQuotID  = ref ~1 : cid ref (* proof/ : {U}{V}{W}{P} prove/ U V W P *)

    fun provePlusExp (U, V, W, P) = Root (Const (!provePlusID),
                                          App (U, App (V, App (W, App (P , Nil)))))
    fun proofPlusExp (U, V, W, P) = Root (Const (!proofPlusID),
                                          App (U, App (V, App (W, App (P , Nil)))))

    fun proofTimesExp (U, V, W, P) = Root (Const (!proofTimesID),
                                           App (U, App (V, App (W, App (P , Nil)))))
    fun proveTimesExp (U, V, W, P) = Root (Const (!proveTimesID),
                                           App (U, App (V, App (W, App (P , Nil)))))

    fun proveQuotExp (U, V, W, P) = Root (Const (!proveQuotID),
                                          App (U, App (V, App (W, App (P , Nil)))))
    fun proofQuotExp (U, V, W, P) = Root (Const (!proofQuotID),
                                          App (U, App (V, App (W, App (P , Nil)))))

    fun numberConDec (d) = ConDec (W.fmt StringCvt.DEC (d), NONE, 0, Normal, word (), Type)

    fun numberExp (d) = Root (FgnConst (!myID, numberConDec (d)), Nil)

    (* scanNumber (str) = numOpt

       Invariant:
         numOpt = SOME(n) if str is the decimal representation of the number n
                = NONE otherwise
    *)
    fun scanNumber (str) =
          let
            fun check (chars as (_ :: _)) =
                 (List.all Char.isDigit chars)
              | check nil =
                  false
          in
            if check (String.explode str)
            then
              case (StringCvt.scanString (W.scan StringCvt.DEC) str)
                of SOME(d) => (if numCheck (d) then SOME(d) else NONE)
                 | NONE => NONE
            else NONE
          end

    (* parseNumber str = SOME(conDec) or NONE

       Invariant:
       If str parses to the number n
       then conDec is the (foreign) constant declaration of n
    *)
    fun parseNumber string =
          case (scanNumber string)
            of SOME(d) => SOME(numberConDec d)
             | NONE => NONE

    fun plusPfConDec (d1, d2) =
          let
            val d3 = W.+ (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "+"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    plusExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    fun plusPfExp ds = Root (FgnConst (!myID, plusPfConDec ds), Nil)

    fun timesPfConDec (d1, d2) =
          let
            val d3 = W.* (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "*"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    timesExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    fun timesPfExp ds = Root(FgnConst (!myID, timesPfConDec ds), Nil)

    fun quotPfConDec (d1, d2) =
          let
            val d3 = W.div (d1, d2)
          in
            ConDec (W.fmt StringCvt.DEC d1
                    ^ "/"
                    ^ W.fmt StringCvt.DEC d2,
                    NONE, 0, Normal,
                    quotExp (numberExp d1, numberExp d2, numberExp d3),
                    Type)
          end

    fun quotPfExp ds = Root (FgnConst (!myID, quotPfConDec ds), Nil)

    fun scanBinopPf oper string =
          let
            val args = String.tokens (fn c => c = oper) string
          in
            case args
              of [arg1, arg2] =>
                (case (StringCvt.scanString (W.scan StringCvt.DEC) arg1,
                       StringCvt.scanString (W.scan StringCvt.DEC) arg2)
                   of (SOME(d1), SOME(d2)) => SOME(d1, d2)
                    | _ => NONE)
               | _ => NONE
          end

    (* parseBinopPf operator string = SOME(conDec) or NONE

       Invariant:
       If string parses to the proof object of n1<operator>n2
       then conDec is the (foreign) constant declaration of n1<operator>n2
    *)
    fun parseBinopPf oper string =
          case (oper, scanBinopPf oper string)
            of (#"+", SOME(ds)) => SOME(plusPfConDec ds)
             | (#"*", SOME(ds)) => SOME(timesPfConDec ds)
             | (#"/", SOME(ds)) => SOME(quotPfConDec ds)
             | _ => NONE

    val parsePlusPf = parseBinopPf #"+"
    val parseTimesPf = parseBinopPf #"*"
    val parseQuotPf = parseBinopPf #"/"

    fun parseAll string =
          (case (parseNumber (string))
             of SOME(conDec) => SOME(conDec)
              | NONE =>
          (case (parsePlusPf (string))
             of SOME(conDec) => SOME(conDec)
              | NONE =>
          (case (parseTimesPf (string))
             of SOME(conDec) => SOME(conDec)
              | NONE => parseQuotPf (string))))

    datatype FixTerm =                                      (* Term                       *)
      Num of W.word                                         (* Term ::= n                 *)
    | PlusPf of (W.word * W.word)                           (*        | n1+n2             *)
    | TimesPf of (W.word * W.word)                          (*        | n1*n2             *)
    | QuotPf of (W.word * W.word)                           (*        | n1/n2             *)
    | Expr of (Exp * Sub)                                   (*        | <Expr>            *)

    (* fromExpW (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V    (U,s)  in whnf
       then t is the internal representation of U[s] as term
    *)
    fun fromExpW (Us as (Root (FgnConst (cs, conDec), _), _)) =
          if (cs = !myID)
          then
            let
              val string = conDecName conDec
            in
              (case (scanNumber string)
                 of SOME(d) => Num d
                  | NONE =>
              (case (scanBinopPf #"/" string)
                 of SOME(ds) => QuotPf ds
                  | NONE =>
              (case (scanBinopPf #"+" string)
                 of SOME(ds) => PlusPf ds
                  | NONE =>
              (case (scanBinopPf #"*" string)
                 of SOME(ds) => TimesPf ds
                  | NONE => Expr Us))))
            end
          else Expr Us
      | fromExpW (Us as (Root (Def(d), _), _)) =
          fromExpW (Whnf.expandDef (Us))
      | fromExpW Us = Expr Us

    (* fromExp (U, s) = t

       Invariant:
       If   G' |- s : G    G |- U : V
       then t is the internal representation of U[s] as term
    *)
    and fromExp Us = fromExpW (Whnf.whnf Us)

    (* toExp t = U

       Invariant:
       G |- U : V and U is the Twelf syntax conversion of t
    *)
    fun toExp (Num d) = numberExp d
      | toExp (PlusPf ds) = plusPfExp ds
      | toExp (TimesPf ds) = timesPfExp ds
      | toExp (QuotPf ds) = quotPfExp ds
      | toExp (Expr Us) = EClo Us

    fun solveNumber (G, S, k) = SOME(numberExp (W.fromInt k))

    (* fst (S, s) = U1, the first argument in S[s] *)
    fun fst (App (U1, _), s) = (U1, s)
      | fst (SClo (S, s'), s) = fst (S, comp (s', s))

    (* snd (S, s) = U2, the second argument in S[s] *)
    fun snd (App (_, S), s) = fst (S, s)
      | snd (SClo (S, s'), s) = snd (S, comp (s', s))

    (* trd (S, s) = U1, the third argument in S[s] *)
    fun trd (App (_, S), s) = snd (S, s)
      | trd (SClo (S, s'), s) = trd (S, comp (s', s))

    (* fth (S, s) = U1, the fourth argument in S[s] *)
    fun fth (App (_, S), s) = trd (S, s)
      | fth (SClo (S, s'), s) = fth (S, comp (s', s))

    fun toInternalPlus (G, U1, U2, U3) () =
          [(G, plusExp(U1, U2, U3))]

    and awakePlus (G, proof, U1, U2, U3) () =
          case (solvePlus (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    (* constraint constructor *)
    and makeCnstrPlus (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepPlus (G, proof, U1, U2, U3))

    (* solvePlus (G, S, n) tries to find the n-th solution to
          G |- '+' @ S : type
    *)
    and solvePlus (G, S, 0) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
          in
            (case (fromExp (Us1), fromExp (Us2), fromExp (Us3))
               of (Num d1, Num d2, Num d3) =>
                     if(d3 = W.+(d1, d2) andalso plusCheck (d1, d2))
                     then SOME(plusPfExp(d1, d2))
                     else NONE
                | (Expr Us1, Num d2, Num d3) =>
                     if (W.>=(d3, d2)
                         andalso Unify.unifiable (G, Us1, (numberExp (W.-(d3, d2)), id)))
                     then SOME(plusPfExp(W.-(d3, d2), d2))
                     else NONE
                | (Num d1, Expr Us2, Num d3) =>
                     if (W.>=(d3, d1)
                         andalso Unify.unifiable (G, Us2, (numberExp (W.-(d3, d1)), id)))
                     then SOME(plusPfExp(d1, W.-(d3, d1)))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (plusCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp (W.+(d1, d2)), id)))
                     then SOME(plusPfExp(d1, d2))
                     else NONE
                | _ => let
                         val proof = newEVar (G, plusExp(EClo Us1, EClo Us2, EClo Us3))
                         val cnstr = makeCnstrPlus (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         val _ = List.app (fn Us => Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solvePlus (G, S, n) = NONE

    and toInternalTimes (G, U1, U2, U3) () =
          [(G, timesExp(U1, U2, U3))]

    and awakeTimes (G, proof, U1, U2, U3) () =
          case (solveTimes (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    and makeCnstrTimes (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepTimes (G, proof, U1, U2, U3))

    (* solveTimes (G, S, n) tries to find the n-th solution to
         G |- '*' @ S : type
    *)
    and solveTimes (G, S, 0) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
          in
            (case (fromExp Us1, fromExp Us2, fromExp Us3)
               of (Num d1, Num d2, Num d3) =>
                     if (d3 = W.*(d1, d2) andalso timesCheck (d1, d2))
                     then SOME(timesPfExp (d1, d2))
                     else NONE
                | (Expr Us1, Num d2, Num d3) =>
                     if (d3 = zero
                         andalso Unify.unifiable
                                   (G, Us1, (numberExp(zero), id)))
                     then SOME(timesPfExp (zero, d2))
                     else if (W.>(d2, zero) andalso W.>(d3, zero)
                              andalso W.mod(d3, d2) = zero
                              andalso
                                Unify.unifiable (G, Us1, (numberExp(W.div (d3, d2)), id)))
                     then SOME(timesPfExp (W.div (d3, d2), d2))
                     else NONE
                | (Num d1, Expr Us2, Num d3) =>
                     if (d3 = zero
                         andalso Unify.unifiable
                                   (G, Us2, (numberExp(zero), id)))
                       then SOME(timesPfExp (d1, zero))
                     else if (W.>(d1, zero) andalso W.>(d3, zero)
                              andalso W.mod(d3, d1) = zero
                              andalso
                                Unify.unifiable
                                  (G, Us2, (numberExp(W.div(d3, d1)), id)))
                     then SOME(timesPfExp (d1, W.div (d3, d1)))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (timesCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp(W.*(d1, d2)), id)))
                     then SOME(timesPfExp (d1, d2))
                     else NONE
                | _ => let
                         val proof = newEVar (G, timesExp(EClo Us1, EClo Us2, EClo Us3))
                         val cnstr = makeCnstrTimes (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         val _ = List.app (fn Us => Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solveTimes (G, S, n) = NONE

    and toInternalQuot (G, U1, U2, U3) () =
          [(G, quotExp(U1, U2, U3))]

    and awakeQuot (G, proof, U1, U2, U3) () =
          case (solveQuot (G, App(U1, App (U2, App (U3, Nil))), 0))
            of SOME(proof') => Unify.unifiable(G, (proof, id), (proof', id))
             | NONE => false

    (* constraint constructor *)
    and makeCnstrQuot (G, proof, U1, U2, U3) =
          FgnCnstr (!myID, MyFgnCnstrRepQuot (G, proof, U1, U2, U3))

    (* solveQuot (G, S, n) tries to find the n-th solution to
         G |- '/' @ S : type
    *)
    and solveQuot (G, S, 0) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
          in
            (case (fromExp Us1, fromExp Us2, fromExp Us3)
               of (Num d1, Num d2, Num d3) =>
                     if (quotCheck (d1, d2) andalso d3 = W.div(d1, d2))
                     then SOME(quotPfExp (d1, d2))
                     else NONE
                | (Num d1, Num d2, Expr Us3) =>
                     if (quotCheck (d1, d2)
                         andalso Unify.unifiable (G, Us3, (numberExp (W.div(d1, d2)), id)))
                     then SOME(quotPfExp (d1, d2))
                     else NONE
                | _ => let
                         val proof = newEVar (G, quotExp (EClo Us1, EClo Us2, EClo Us3))
                         val cnstr = makeCnstrQuot (G, proof, EClo Us1, EClo Us2, EClo Us3)
                         val _ = List.app (fn Us => Unify.delay (Us, ref cnstr))
                                          [Us1, Us2, Us3]
                       in
                         SOME(proof)
                       end)
          end
      | solveQuot (G, S, n) = NONE

    (* solveProvePlus (G, S, n) tries to find the n-th solution to
         G |- prove+ @ S : type
    *)
    fun solveProvePlus (G, S, k) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
            val Us4 = fth (S, id)
          in
            case (solvePlus (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofPlusExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    (* solveProveTimes (G, S, n) tries to find the n-th solution to
         G |- prove* @ S : type
    *)
    fun solveProveTimes (G, S, k) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
            val Us4 = fth (S, id)
          in
            case (solveTimes (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofTimesExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    (* solveProveQuot (G, S, n) tries to find the n-th solution to
         G |- prove/ @ S : type
    *)
    fun solveProveQuot (G, S, k) =
          let
            val Us1 = fst (S, id)
            val Us2 = snd (S, id)
            val Us3 = trd (S, id)
            val Us4 = fth (S, id)
          in
            case (solveQuot (G, App (EClo Us1, App (EClo Us2, App (EClo Us3, Nil))), k))
              of SOME(U) =>
                   if Unify.unifiable(G, Us4, (U, id))
                   then SOME(proofQuotExp (EClo Us1, EClo Us2, EClo Us3, EClo Us4))
                   else NONE
               | NONE => NONE
          end

    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)
    fun pi (name, U, V) = Pi ((Dec (SOME(name), U), Maybe), V)
    fun bvar n = Root (BVar n, Nil)

    fun installFgnCnstrOps () = let
        val csid = !myID
        val _ = FgnCnstrStd.ToInternal.install (csid,
                                                (fn (MyFgnCnstrRepPlus (G, _, U1, U2, U3)) => toInternalPlus (G, U1, U2, U3)
                                                  | (MyFgnCnstrRepTimes (G, _, U1, U2, U3)) => toInternalTimes (G, U1, U2, U3)
                                                  | (MyFgnCnstrRepQuot (G, _, U1, U2, U3)) => toInternalQuot (G, U1, U2, U3)
                                                  | fc => raise (UnexpectedFgnCnstr fc)))
        val _ = FgnCnstrStd.Awake.install (csid,
                                           (fn (MyFgnCnstrRepPlus (G, proof, U1, U2, U3)) => awakePlus (G, proof, U1, U2, U3)
                                             | (MyFgnCnstrRepTimes (G, proof, U1, U2, U3)) => awakeTimes (G, proof, U1, U2, U3)
                                             | (MyFgnCnstrRepQuot (G, proof, U1, U2, U3)) => awakeQuot (G, proof, U1, U2, U3)
                                             | fc => raise (UnexpectedFgnCnstr fc)))
        val _ = FgnCnstrStd.Simplify.install (csid,
                                              (fn (MyFgnCnstrRepPlus _) => (fn () => false)
                                                | (MyFgnCnstrRepTimes _) => (fn () => false)
                                                | (MyFgnCnstrRepQuot _) => (fn () => false)
                                                | fc => raise (UnexpectedFgnCnstr fc)))
    in
        ()
    end

    (* init (cs, installFunction) = ()
       Initialize the constraint solver.
       installFunction is used to add its signature symbols.
    *)
    fun init (cs, installF) =
          (
            myID := cs;

            wordID :=
              installF (ConDec ("word" ^ Int.toString(wordSize'), NONE, 0,
                                Constraint (!myID, solveNumber),
                                Uni (Type), Kind),
                        NONE : FX.fixity option, [MS.Mnil]);

            plusID :=
              installF (ConDec ("+", NONE, 0,
                                Constraint (!myID, solvePlus),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Minus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            timesID :=
              installF (ConDec ("*", NONE, 0,
                                Constraint (!myID, solveTimes),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Minus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            quotID :=
              installF (ConDec ("/", NONE, 0,
                                Constraint (!myID, solveQuot),
                                arrow (word (),
                                  arrow (word (),
                                    arrow (word (), Uni (Type)))), Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Plus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Minus, SOME "Z"), MS.Mnil))),
                         MS.Mapp(MS.Marg(MS.Plus, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Minus, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Plus, SOME "Z"), MS.Mnil)))]);

            provePlusID :=
              installF (ConDec ("prove+", NONE, 0,
                                Constraint (!myID, solveProvePlus),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", plusExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);
            proofPlusID :=
              installF (ConDec ("proof+", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", plusExp (bvar 3, bvar 2, bvar 1),
                                          provePlusExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            proveTimesID :=
              installF (ConDec ("prove*", NONE, 0,
                                Constraint (!myID, solveProveTimes),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", timesExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);

            proofTimesID :=
              installF (ConDec ("proof*", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", timesExp (bvar 3, bvar 2, bvar 1),
                                          proveTimesExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            proveQuotID :=
              installF (ConDec ("prove/", NONE, 0,
                                Constraint (!myID, solveProveQuot),
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", quotExp (bvar 3, bvar 2, bvar 1),
                                          Uni (Type))))),
                                Kind),
                        NONE,
                        [MS.Mapp(MS.Marg(MS.Star, SOME "X"),
                                 MS.Mapp(MS.Marg(MS.Star, SOME "Y"),
                                         MS.Mapp(MS.Marg(MS.Star, SOME "Z"),
                                                 MS.Mapp(MS.Marg(MS.Star, SOME "P"),
                                                         MS.Mnil))))]);

            proofQuotID :=
              installF (ConDec ("proof/", NONE, 0, Normal,
                                pi ("X", word (),
                                  pi ("Y", word (),
                                    pi ("Z", word (),
                                      pi ("P", quotExp (bvar 3, bvar 2, bvar 1),
                                          proveQuotExp (bvar 4, bvar 3, bvar 2, bvar 1))))),
                                Type),
                        NONE, nil);

            installFgnCnstrOps ();
            ()
          )
  in
    val solver =
          {
            name = "word" ^ Int.toString(wordSize'),
            keywords = "numbers,equality",
            needs = ["Unify"],

            fgnConst = SOME({parse = parseAll}),

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          }
  end
end  (* functor CSIntWord *)
