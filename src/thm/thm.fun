(* Theorem and Related Declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor Thm (structure Global : GLOBAL
             structure ThmSyn': THMSYN
             structure TabledSyn : TABLEDSYN
             structure ModeTable : MODETABLE
             structure Order : ORDER
             (*! sharing Order.IntSyn = ThmSyn'.ModeSyn.IntSyn !*)
             structure ThmPrint : THMPRINT
               sharing ThmPrint.ThmSyn = ThmSyn'
               (*! structure Paths' : PATHS !*)
               )
  : THM =
struct
  structure ThmSyn = ThmSyn'
  (*! structure Paths = Paths' !*)
  structure TabledSyn = TabledSyn

  (* -bp *)
  datatype Order = Varg | Lex of Order list | Simul of Order list

  exception Error of string

  local
    structure L = ThmSyn
    structure M = ModeSyn  (* L.ModeSyn *)
    structure I = IntSyn
    structure P = ThmPrint
    structure O = Order
    fun error (r, msg) = raise Error (Paths.wrap (r, msg))

    (* To check validity of a termination declaration  O C
       we enforce that all variable names which occur in C must be distinct
       and if C = C1 .. Cm then we ensure that for all Varg (X1 .. Xn) in O,

           1) n = m
       and 2) each Ci contains an occurrence of Xi
    *)

    (* unique (((a, P), r), A) = A'

       Invariant:
       If   A is a list of variables already collected in a call pattern
       and  P does not contain any variables in A
       then A' = A, Var (P)
       else exception Error is raised.
       (r is region information for error message)
    *)
    fun unique (((a, P), r), A) =
      let
        fun unique' (I.Uni _, nil, A) = A
          | unique' (I.Pi (_, V), NONE :: P, A) = unique' (V, P, A)
          | unique' (I.Pi (_, V), SOME x :: P, A) =
             (List.app (fn x' => if x = x'
                                   then error (r, "Variable " ^ x ^ " used more than once")
                                 else ()) A;
              unique' (V, P, x :: A))
          | unique' (I.Uni _, _, _) = error (r, "Too many arguments supplied to type family "
                                                ^ Names.qidToString (Names.constQid a))
          | unique' (I.Pi (_, V), nil, _) = error (r, "Too few arguments supplied to type family "
                                                   ^ Names.qidToString (Names.constQid a))
          | unique' (I.Root _, _, _) = error (r, "Constant " ^ Names.qidToString (Names.constQid a) ^
                                              " is an object, not a type family")

        fun skip (0, V, P, A) = unique' (V, P, A)
          | skip (k, I.Pi (_, V), P, A) = skip (k-1, V, P, A)

      in
        skip (I.constImp a, I.constType a, P, A)
      end

    (* uniqueCallpats (L, rs) = ()

       Invariant:
       If   L is a callpattern
       and  each variable in L is unique
       then uniqueCallpats returns ()
       else exception Error is raised.

       (rs is a list of region information for error message,
       each region corresponds to one type in the call pattern,
       in order)
    *)
    fun uniqueCallpats (L, rs) =
        let
          fun uniqueCallpats' ((nil, nil), A) = ()
            | uniqueCallpats' ((aP :: L, r :: rs), A) =
                uniqueCallpats' ((L, rs), unique ((aP, r), A))
        in
          uniqueCallpats' ((L, rs), nil)
        end

    (* wfCallpats (L, C, r) = ()

       Invariant:
       If   L is a list of variable names of a virtual argument
       and  C is a call pattern, the predicate in C has a mode
       then wfCallpats terminates with () if
            1) there are as many call patterns as variable names
            2) each variable name occurs in a different call pattern
       else exception Error is raised
       (r region information, needed for error messages)
    *)
    fun wfCallpats (L0, C0, r) =
        let
          fun makestring nil = ""
            | makestring (s :: nil) = s
            | makestring (s :: L) = s ^ " " ^ (makestring L)

          fun exists' (x, nil, _) = false
            | exists' (x, NONE :: L, M.Mapp (_, mS)) =
                exists' (x, L, mS)
            | exists' (x, SOME y :: L, M.Mapp (M.Marg (mode, _), mS)) =
              if x = y then
                (case mode
                   of M.Plus => true
                 | _ => error (r, "Expected " ^ x ^ " to have " ^ M.modeToString M.Plus
                                  ^ " mode"))
              else exists' (x, L, mS)

          (* skip (i, x, P, mS)  ignores first i argument in modeSpine mS,
             then returns true iff x occurs in argument list P
             Effect: raises Error if position of x is not input (+).
          *)
          fun skip (0, x, P, mS) = exists' (x, P, mS)
            | skip (k, x, P, M.Mapp (_, mS)) = skip (k-1, x, P, mS)

          fun delete (x, (aP as (a, P)) :: C) =
              if skip (I.constImp a, x, P, valOf (ModeTable.modeLookup a)) (* exists by invariant *)
                then C
              else aP :: delete (x, C)
            | delete (x, nil) = error (r, "Variable " ^ x ^ " does not occur as argument")

          fun wfCallpats' (nil, nil) = ()
            | wfCallpats' (x :: L, C) =
                wfCallpats' (L, delete (x, C))
            | wfCallpats' _ =
                error (r, "Mutual argument (" ^ makestring L0
                          ^ ") does not cover all call patterns")
        in
          wfCallpats' (L0, C0)
        end

    (* wf ((O, C), (r, rs)) = ()

       Invariant:
       If   O is an order
       and  C is a call pattern
       then wf terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
    fun wf ((O, L.Callpats C), (r, rs)) =
        let
          fun wfOrder (L.Varg L) = wfCallpats (L, C, r)
            | wfOrder (L.Lex L) = wfOrders L
            | wfOrder (L.Simul L) = wfOrders L

          and wfOrders (nil) = ()
            | wfOrders (O :: L) = (wfOrder O; wfOrders L)
          fun allModed (nil) = ()
            | allModed ((a, P) :: Cs) =
              (case ModeTable.modeLookup a
                 of NONE => error (r, "Expected " ^ Names.qidToString (Names.constQid a)
                                      ^ " to be moded")
                  | SOME mS => ();
               allModed Cs)
        in
          (allModed C; uniqueCallpats (C, rs); wfOrder O)
        end

    (* argPos (x, L, n) = nOpt

       Invariant:
       If   x is a variable name
       and  L is a list of argument for a call pattern
       and  n is the position of the first argument name in L
            in the call pattern
       then nOpt describes the optional  position of the occurrence
    *)
    fun argPos (x, nil, n) = NONE
      | argPos (x, NONE :: L, n) =
          argPos (x, L, n+1)
      | argPos (x, SOME x' :: L, n) =
          if x = x' then SOME n
          else argPos (x, L, n+1)

    (* locate (L, P, n) = n'

       Invariant:
       If   L is a list of variable names (as part of a virtual argument)
       and  P is an argument list (from a call pattern)
       and  n is the position of the first argument name in P
            in the call pattern
       then n' describes the position of the virtual argument in P
    *)
    fun locate (x :: vars, params, imp) =
        case argPos (x, params, imp+1)
          of NONE => locate (vars, params, imp)
           | SOME n => n
     (* locate nil cannot occur by invariant *)

    (* argOrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
    fun argOrder (L.Varg L, P, n) = O.Arg (locate (L, P, n))
      | argOrder (L.Simul L, P, n) = O.Simul (argOrderL (L, P, n))
      | argOrder (L.Lex L, P, n) = O.Lex (argOrderL (L, P, n))

    and argOrderL (nil, P, n) = nil
      | argOrderL (O :: L, P, n) = argOrder (O, P, n) :: argOrderL (L, P, n)


    (*  argOrderMutual (C, k, A) = A'

        Invariant:

        If   C is a list of call patterns
        and  k is a function, mapping a call patterns to 'a
        and  A is an acculmulator for objects of type 'a
        then A' is an accumulator extending A containing all
             images of C under k.
    *)
    fun argOrderMutual (nil, k, A) = A
      | argOrderMutual (P :: L, k, A) =
          argOrderMutual (L, k, k (P, A))

    (* installorder (O, LE, LT) = ()

       Invariant:
       If   O is an order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument order with type families.
    *)
    fun installOrder (_, nil, _) = ()
      | installOrder (O, (aP as (a, P)) :: thmsLE, thmsLT) =
        let
          val M' = argOrderMutual (thmsLE, fn ((a, _), L) => O.LE (a, L),
                                    argOrderMutual (aP :: thmsLT,
                                                     fn ((a, _), L) => O.LT (a, L), O.Empty))
          val O' = argOrder (O, P, I.constImp a)
          val S' = O.install (a, O.TDec (O',M'))
        in
          installOrder (O, thmsLE, aP :: thmsLT)
        end

    (* installDecl (O, C) = L'

       Invariant:
       If   O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: All orders are stored
    *)
    fun installDecl (O, L.Callpats L) =
        (installOrder (O, L, nil);
         map (fn (a, _) => a) L)

    (* installTerminates (T, (r,rs)) = L'

       Invariant:
       If   T is a termination declaration of (O, C)
       and  O is an order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (O, C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
    fun installTerminates (L.TDecl T, rrs) = (wf (T, rrs); installDecl T)

    fun uninstallTerminates cid = O.uninstall cid

    (* installTotal (T, (r, rs)) = L'
       Invariant as in installTerminates
    *)
    fun installTotal (L.TDecl T, rrs) = (wf (T, rrs); installDecl T)

    fun uninstallTotal cid = O.uninstall cid

    (* -bp *)

    (* argROrder (O, P, n) = O'

       Invariant:
       If   O is an order
       and  P is the argument spine of a call pattern
       and  n is the number of implicit arguments of the
                 call pattern
       then O' is an order where all virtual arguments are
                  replaced by positions

    *)
    fun argROrder (L.Varg L, P, n) = O.Arg (locate (L, P, n))
      | argROrder (L.Simul L, P, n) = O.Simul (argROrderL (L, P, n))
      | argROrder (L.Lex L, P, n) = O.Lex (argROrderL (L, P, n))

    and argROrderL (nil, P, n) = nil
      | argROrderL (O :: L, P, n) = argROrder (O, P, n) :: argROrderL (L, P, n)

    fun argPredicate (L.Less, O, O') = O.Less (O, O')
      | argPredicate (L.Leq, O, O') = O.Leq (O, O')
      | argPredicate (L.Eq, O, O') = O.Eq (O, O')

    (* installPredicate (name, R, LE, LT) = ()

       Invariant:
       If   R is a reduction order,
       and  LE is a list of callpatterns where ind. argument must LT decrease
       and  LT is a list of callpatterns where ind. argument must LE decrease
       then installorder terminates with ()

       Effect: updates table associating argument reduction order with
               type families.

    *)
    fun installPredicate ( _, nil, _) = ()
      | installPredicate (L.RedOrder(Pred,O1, O2), (aP as (a, P)) :: thmsLE, thmsLT) =
        let
          val M' = argOrderMutual (thmsLE, fn ((a, _), L) => O.LE (a, L),
                                   argOrderMutual (aP :: thmsLT,
                                                   fn ((a, _), L) => O.LT (a, L), O.Empty))
          val O1' = argROrder (O1, P, I.constImp a)
          val O2' = argROrder (O2, P, I.constImp a)
          val pr  = argPredicate (Pred, O1', O2')
          (* install termination order *)
          (* bug: %reduces should not entail %terminates *)
          (* fixed: Sun Mar 13 09:41:18 2005 -fp *)
          (* val S'  = O.install (a, O.TDec (O2', M')) *)
          (* install reduction order   *)
          val S'' = O.installROrder (a, O.RDec (pr, M'))
        in
          installPredicate (L.RedOrder(Pred,O1, O2), thmsLE, aP :: thmsLT)
        end

    (* installRDecl (R, C) = L'

       Invariant:
       If   R is a reduction order
       and  C is a call pattern
       then L' is a list of all type families mentioned in C

       Effect: reduction order is stored
    *)
    fun installRDecl (R, L.Callpats L) =
        (installPredicate (R, L, nil);
         map (fn (a, _) => a) L)

    (* wfRCallpats
       well-formed call pattern in a reduction declaration
       pattern does not need to be moded
       Tue Apr 30 10:32:31 2002 -bp
     *)

    fun wfRCallpats (L0, C0, r) =
        let
          fun makestring nil = ""
            | makestring (s :: nil) = s
            | makestring (s :: L) = s ^ " " ^ (makestring L)

          fun exists' (x, nil) = false
            | exists' (x, NONE :: L) =
                exists' (x, L)
            | exists' (x, SOME y :: L) =
              if x = y
                then true
              else exists' (x, L)

          fun delete (x, (aP as (a, P)) :: C) =
              (if exists' (x, P)
                 then C
               else aP :: delete (x, C))
            | delete (x, nil) = error (r, "Variable " ^ x ^ " does not occur as argument")

          fun wfCallpats' (nil, nil) = ()
            | wfCallpats' (x :: L, C) =
                wfCallpats' (L, delete (x, C))
            | wfCallpats' _ =
                error (r, "Mutual argument (" ^ makestring L0
                          ^ ") does not cover all call patterns")
        in
          wfCallpats' (L0, C0)
        end

 (* wfred ((Red(Pred,O.O'), C), (r, rs)) = ()

       Invariant:
       If   O,O' is an order and Pred is some predicate
       and  C is a call pattern
       then wfred terminates with ()
            if C contains pairwise different variable names
            and each virtual argument in O covers all call patterns.
       else exception Error is raised
       (r, rs  region information, needed for error messages)
    *)
    fun wfred ((L.RedOrder(Pred,O,O'), L.Callpats C), (r, rs)) =
        let
          fun wfOrder (L.Varg L) = (wfRCallpats (L, C, r) ; Varg)
            | wfOrder (L.Lex L) = Lex(wfOrders L)
            | wfOrder (L.Simul L) = Simul(wfOrders L)

          and wfOrders nil = nil
            | wfOrders (O :: L) = (wfOrder O) :: (wfOrders L)
        in
          (uniqueCallpats (C, rs);
          if  wfOrder O = wfOrder O' then
              ()
          else
              error (r, "Reduction Order (" ^ P.ROrderToString (L.RedOrder(Pred,O,O')) ^
                           ") requires both orders to be of the same type.")
              )
        end


    (* installRedOrder (R, (r,rs)) = L'

       Invariant:
       If   R is a reduction declaration of (pred(O,O'), C)
       and  O,O' is an order
       and pred is a predicate
       and  C is a call pattern
       then L' is a list of all type families mentioned in C
            if (pred(O,O'), C) is well-formed
            else exception Error is raised
       (r is region information of O
        rs is a list of regions of C
        used for error messages)
    *)
    fun installReduces (L.RDecl (R, C), rrs) = (wfred ((R, C), rrs); installRDecl (R, C))
    fun uninstallReduces cid = O.uninstallROrder cid

    fun installTabled (L.TabledDecl cid) = TabledSyn.installTabled cid

    fun installKeepTable (L.KeepTableDecl cid) = TabledSyn.installKeepTable cid

  in
    val installTotal = installTotal
    val uninstallTotal = uninstallTotal
    val installTerminates = installTerminates
    val uninstallTerminates = uninstallTerminates
    val installReduces = installReduces
    val uninstallReduces = uninstallReduces
    val installTabled = installTabled
    val installKeepTable = installKeepTable
  end (* local *)

end; (* functor Thm *)
