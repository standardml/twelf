(* String Equation Solver *)
(* Author: Roberto Virga *)

functor CSEqStrings (structure IntSyn : INTSYN
                     structure Whnf : WHNF
                       sharing Whnf.IntSyn = IntSyn
                     structure Unify : UNIFY
                       sharing Unify.IntSyn = IntSyn
                     structure CSManager : CS_MANAGER
                       sharing CSManager.IntSyn = IntSyn)
 : CS =
struct
  structure CSManager = CSManager

  local
    open IntSyn

    structure FX = CSManager.Fixity
    structure MS = CSManager.ModeSyn

    val myID = ref ~1 : IntSyn.csid ref

    val stringID = ref ~1 : IntSyn.cid ref

    fun string () = Root (Const (!stringID), Nil)

    val concatID = ref ~1 : IntSyn.cid ref

    fun concatExp (U, V) = Root (Const (!concatID), App (U, App (V, Nil)))

    fun toString s = ("\"" ^ s ^ "\"")

    fun stringConDec (str) = ConDec (toString (str), 0, Normal, string (), Type)
    fun stringExp (str) = Root (FgnConst (!myID, stringConDec (str)), Nil)

    fun fromString string =
          let
            val len = String.size string
          in
            if (String.sub (string, 0) = #"\"")
              andalso (String.sub (string, len-1) = #"\"")
            then
              SOME (String.substring (string, 1, len-2))
            else
              NONE
          end

    fun parseString string =
          (case fromString (string)
             of SOME(str) => SOME(stringConDec (str))
              | NONE => NONE)

    fun solveString (G, S, k) = SOME(stringExp (Int.toString k))

    datatype Concat =
      Concat of Atom list

    and Atom =
      String of string
    | Exp of IntSyn.eclo

    fun fromExpW (Us as (FgnExp (cs, ops), _)) =
          if (cs = !myID)
          then recoverConcat (#toInternal(ops) ())
          else Concat [Exp Us]
      | fromExpW (Us as (Root (FgnConst (cs, conDec), _), _)) =
          if (cs = !myID)
          then (case fromString (conDecName (conDec))
                  of SOME(str) => if (str = "") then Concat nil
                                  else Concat [String str])
          else Concat [Exp Us]
      | fromExpW Us =
          Concat [Exp Us]
    and fromExp Us =
          fromExpW (Whnf.whnf Us)

    and recoverConcat (U as Root (Const (cid), App (U1, App (U2, Nil)))) =
          if (cid = !concatID)
          then
            let
              val Concat AL1 = fromExp (U1, id)
              val Concat AL2 = recoverConcat U2
            in
              Concat (AL1 @ AL2)
            end
          else
            fromExp (U, id)
      | recoverConcat U = fromExp (U, id)

    fun toExp (Concat nil) = stringExp ""
      | toExp (Concat [String str]) = stringExp str
      | toExp (Concat [Exp (U, Shift(0))]) = U
      | toExp (Concat [Exp Us]) = EClo Us
      | toExp (Concat (A :: AL)) =
          concatExp (toExp (Concat [A]), toExp (Concat AL))

    fun catConcat (Concat nil, concat2) = concat2
      | catConcat (concat1, Concat nil) = concat1
      | catConcat (Concat AL1, Concat AL2) =
          (case (List.rev AL1, AL2)
             of ((String str1) :: revAL1', (String str2) :: AL2') =>
               Concat ((List.rev revAL1') @ ((String (str1 ^ str2)) :: AL2'))
              | (_, _) => Concat (AL1 @ AL2))

    fun normalize (concat as (Concat nil)) = concat
      | normalize (concat as (Concat [String str])) = concat
      | normalize (Concat [Exp Us]) = fromExp Us
      | normalize (Concat (A :: AL)) =
          catConcat (normalize (Concat [A]), normalize(Concat AL))

    fun mapConcat (f, Concat AL) =
          let
            fun mapConcat' nil = nil
              | mapConcat' ((Exp Us) :: AL) =
                  (Exp (f (EClo Us), id)) :: mapConcat' AL
              | mapConcat' ((String str) :: AL) =
                  (String str) :: mapConcat' AL
          in
            Concat (mapConcat' AL)
          end

    datatype Split = Split of string * string

    datatype Decomp = Decomp of string * string list

    fun index (str1, str2) =
          let
            val max = (String.size str2) - (String.size str1)
            fun index' i =
                  if (i <= max)
                  then
                    if String.isPrefix str1 (String.extract (str2, i, NONE))
                    then i :: index' (i+1)
                    else index' (i+1)
                  else
                    nil
          in
            index' 0
          end

    fun split (str1, str2) =
          let
            val len = String.size str1
            fun split' i =
                  Split (String.extract (str2, 0, SOME(i)),
                         String.extract (str2, i+len, NONE))
          in
            List.map split' (index (str1, str2))
          end

    datatype StringUnify =
      MultAssign of (Dec Ctx * Exp * Exp * Sub) list
    | MultDelay of Exp list * Cnstr ref
    | Failure

    fun toFgnUnify (MultAssign L) =
          IntSyn.Succeed (List.map (fn GXUss => Assign GXUss) L)
      | toFgnUnify (MultDelay (UL, cnstr)) =
          IntSyn.Succeed (List.map (fn U => Delay (U, cnstr)) UL)
      | toFgnUnify (Failure) = Fail

    fun unifyString (G, Concat AL, str, cnstr) =
          let
            fun unifyString' (AL, nil) =
                  (Failure, nil)
              | unifyString' (nil, [Decomp (parse, parsedL)]) =
                  (MultAssign nil, parse :: parsedL)
              | unifyString' (nil, candidates) =
                  (MultDelay (nil, cnstr), nil)
             | unifyString' ((Exp Us1) :: (Exp Us2) :: AL, _) =
                  (MultDelay ([EClo Us1, EClo Us2], cnstr), nil)
              | unifyString' ((Exp (U as (EVar (r, _, _, _)), s)) :: AL, candidates) =
                  if (Whnf.isPatSub s)
                  then
                    let
                      fun assign r nil = NONE
                        | assign r ((_, EVar (r', _, _, _),
                                        Root (FgnConst (cs, conDec), Nil), _) :: L) =
                            if (r = r') then fromString (conDecName (conDec))
                            else assign r L
                        | assign r (_ :: L) = assign r L
                    in
                      (case unifyString' (AL, candidates)
                         of (MultAssign L, parsed :: parsedL) =>
                               (case (assign r L)
                                  of NONE =>
                                       let
                                         val ss = Whnf.invert s
                                         val W = stringExp(parsed)
                                       in
                                         (MultAssign ((G, U, W, ss) :: L), parsedL)
                                       end
                                   | SOME(parsed') =>
                                       if (parsed = parsed')
                                       then (MultAssign L, parsedL)
                                       else (Failure, nil))
                          | (MultDelay (UL, cnstr), _) =>
                               (MultDelay ((EClo (U, s)) :: UL, cnstr), nil)
                          | (Failure, _) => (Failure, nil))
                    end
                  else (MultDelay ([EClo (U, s)], cnstr), nil)
              | unifyString' ((Exp Us) :: AL, _) =
                  (MultDelay ([EClo Us], cnstr), nil)
              | unifyString' ([String str], candidates) =
                  let
                    fun successors (Decomp (parse, parsedL)) =
                          List.mapPartial (fn (Split (prefix, "")) =>
                                                 SOME (Decomp (prefix, parsedL))
                                            | (Split (prefix, suffix)) => NONE)
                                          (split (str, parse))
                    val candidates' =
                          List.foldr op@ nil (List.map successors candidates)
                  in
                    unifyString' (nil, candidates')
                  end                 
              | unifyString' ((String str) :: AL, candidates) =
                  let
                    fun successors (Decomp (parse, parsedL)) =
                          List.map (fn (Split (prefix, suffix)) =>
                                          Decomp (suffix, prefix :: parsedL))
                                   (split (str, parse))
                    val candidates' =
                          List.foldr op@ nil (List.map successors candidates)
                  in
                    unifyString' (AL, candidates')
                  end
          in
            (case unifyString' (AL, [Decomp(str, nil)])
               of (result, nil) => result
                | (result, [""]) => result
                | (result, parsedL) => Failure)
          end

    fun unifyConcat (G, concat1 as (Concat AL1), concat2 as (Concat AL2)) =
          let
            val U1 = toFgn concat1
            val U2 = toFgn concat2
            val cnstr = ref (Eqn (G, U1, U2))
          in
            (case (AL1, AL2)
               of (nil, nil) => MultAssign nil
                | (nil, _) => Failure
                | (_, nil) => Failure
                | ([String str1], [String str2]) =>
                 if (str1 = str2) then (MultAssign nil) else Failure
                | ([Exp (U as (EVar(r, _, _, _)), s)], _) =>
                    if (Whnf.isPatSub s)
                    then
                      let
                        val ss = Whnf.invert s
                      in
                        if Unify.invertible (G, (U2, id), ss, r)
                        then (MultAssign [(G, U, U2, ss)])
                        else MultDelay ([U1, U2], cnstr)
                      end
                    else
                      MultDelay ([U1, U2], cnstr)
                | (_, [Exp (U as (EVar(r, _, _, _)), s)]) =>
                    if (Whnf.isPatSub s)
                    then
                      let
                        val ss = Whnf.invert s
                      in
                        if Unify.invertible (G, (U1, id), ss, r)
                        then (MultAssign [(G, U, U1, ss)])
                        else MultDelay ([U1, U2], cnstr)
                      end
                    else
                      MultDelay ([U1, U2], cnstr)
                | ([String str], _) =>
                    unifyString (G, concat2, str, cnstr)
                | (_, [String str]) =>
                    unifyString (G, concat1, str, cnstr)
                | _ =>
                  MultDelay ([U1, U2], cnstr))
          end

    and toFgn (concat as (Concat [String str])) = stringExp (str)
      | toFgn (concat as (Concat [Exp Us])) = EClo Us
      | toFgn (concat) =
          FgnExp (!myID,
                  {
                    toInternal = (fn () => toExp (normalize (concat))),

                    map = (fn f =>
                              toFgn (normalize (mapConcat (f, concat)))),
                    unifyWith = (fn (G, U2) =>
                                   toFgnUnify (unifyConcat (G, normalize (concat), 
                                                               fromExp (U2, id)))),
                    equalTo = (fn U2 => false)
                  })

    fun makeFgn (arity, opExp) (S) =
          let
            fun makeParams 0 = Nil
              | makeParams n =
                  App (Root(BVar (n), Nil), makeParams (n-1))
            fun makeLam E 0 = E
              | makeLam E n = 
                  Lam (Dec (NONE, string()), makeLam E (n-1))
            fun expand ((Nil, s), arity) =
                  (makeParams arity, arity)
              | expand ((App (U, S), s), arity) =
                  let
                    val (S', arity') = expand ((S, s), arity-1)
                  in
                    (App (EClo (U, comp (s, Shift (arity'))), S'), arity')
                  end 
              | expand ((SClo (S, s'), s), arity) =
                  expand ((S, comp (s, s')), arity)
            val (S', arity') = expand ((S, id), arity)
          in
            makeLam (toFgn (opExp S')) arity'
          end

    fun makeFgnBinary opConcat =
          makeFgn (2, 
            fn (App (U1, App (U2, Nil))) =>
              opConcat (fromExp (U1, id), fromExp (U2, id)))

    fun arrow (U, V) = Pi ((Dec (NONE, U), No), V)

    fun init (cs, installF) =
          (
            myID := cs;

            stringID := 
              installF (ConDec ("string", 0, Constraint (!myID, solveString),
                                Uni (Type), Kind),
                        NONE, SOME(MS.Mnil));

            concatID :=
              installF (ConDec ("++", 0,
                                Foreign (!myID, makeFgnBinary catConcat),
                                arrow (string (), arrow (string (), string ())),
                                Type),
                        SOME(FX.Infix (FX.maxPrec, FX.Right)), NONE);
            ()
          )
  in
    val solver =
          {
            name = "equality/strings",
            keywords = "strings,equality",
            needs = ["Unify"],

            fgnConst = SOME({parse = parseString}),

            init = init,

            reset  = (fn () => ()),
            mark   = (fn () => ()),
            unwind = (fn () => ())
          } : CSManager.solver

  end
end  (* functor CSEqStrings *)
