(* Meta Prover Interface *)
(* Author: Carsten Schuermann *)

functor Interactive
  (structure Global : GLOBAL
   (*! structure IntSyn' : INTSYN !*)
   (*! structure Tomega' : TOMEGA !*)
   (*! sharing Tomega'.IntSyn = IntSyn' !*)
   structure State' : STATE
   (*! sharing State'.IntSyn = IntSyn' !*)
   (*! sharing State'.Tomega = Tomega' !*)
   structure Formatter : FORMATTER
   structure Trail : TRAIL
   structure Ring : RING
   structure Names : NAMES
   (*! sharing Names.IntSyn = IntSyn' !*)
   structure Weaken : WEAKEN
   (*! sharing Weaken.IntSyn = IntSyn' !*)
   (* structure ModeSyn : MODESYN *)
   (*! sharing ModeSyn.IntSyn = IntSyn' !*)
   structure WorldSyn : WORLDSYN
   (*! sharing WorldSyn.IntSyn = IntSyn' !*)
   (*! sharing WorldSyn.Tomega = Tomega' !*)
   structure Introduce : INTRODUCE
   (*! sharing Introduce.IntSyn = IntSyn' !*)
   (*! sharing Introduce.Tomega = Tomega' !*)
     sharing Introduce.State = State'
   structure Elim : ELIM
   (*! sharing Elim.IntSyn = IntSyn' !*)
   (*! sharing Elim.Tomega = Tomega' !*)
     sharing Elim.State = State'
   structure Split : SPLIT
   (*! sharing Split.IntSyn = IntSyn' !*)
   (*! sharing Split.Tomega = Tomega' !*)
     sharing Split.State = State'
   structure FixedPoint : FIXEDPOINT
   (*! sharing FixedPoint.IntSyn = IntSyn' !*)
   (*! sharing FixedPoint.Tomega = Tomega' !*)
     sharing FixedPoint.State = State'
   structure Fill : FILL
   (*! sharing Fill.IntSyn = IntSyn' !*)
   (*! sharing Fill.Tomega = Tomega' !*)
     sharing Fill.State = State')
  : INTERACTIVE =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Tomega = Tomega' !*)
  structure State = State'

  exception Error = State'.Error

  local
    structure I = IntSyn
    structure T = Tomega
    structure S = State
    structure M = ModeSyn
    structure W = WorldSyn

    fun abort s =
        (print ("* " ^ s ^ "\n");
         raise Error s)

    (* this is pretty preliminary:
       I think we should just adapt the internal representation for formulas
    *)
    fun convertOneFor cid =
      let
        val V  = case I.sgnLookup cid
                   of I.ConDec (name, _, _, _, V, I.Kind) => V
                    | _ => raise Error "Type Constant declaration expected"
        val mS = case ModeTable.modeLookup cid
                   of NONE => raise Error "Mode declaration expected"
                    | SOME mS => mS

        (* convertFor' (V, mS, w1, w2, n) = (F', F'')

           Invariant:
           If   G |- V = {{G'}} type :kind
           and  G |- w1 : G+
           and  G+, G'+, G- |- w2 : G
           and  G+, G'+, G- |- ^n : G+
           and  mS is a spine for G'
           then F'  is a formula excepting a another formula as argument s.t.
                If G+, G'+ |- F formula,
                then . |- F' F formula
           and  G+, G'+ |- F'' formula
        *)
        fun convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Plus, _), mS), w1, w2, n) =
            let
              val (F', F'') = convertFor' (V, mS, I.dot1 w1, I.Dot (I.Idx n, w2), n-1)
            in
              (fn F => T.All ((T.UDec (Weaken.strengthenDec (D, w1)), T.Explicit), F' F), F'')
            end
          | convertFor' (I.Pi ((D, _), V), M.Mapp (M.Marg (M.Minus, _), mS), w1, w2, n) =
            let
              val (F', F'') = convertFor' (V, mS, I.comp (w1, I.shift), I.dot1 w2, n+1)
            in
              (F', T.Ex ((I.decSub (D, w2), T.Explicit), F''))
            end
          | convertFor' (I.Uni I.Type, M.Mnil, _, _, _) =
              (fn F => F, T.True)
          | convertFor' _ = raise Error "type family must be +/- moded"

        (* shiftPlus (mS) = s'

         Invariant:
         s' = ^(# of +'s in mS)
         *)

        fun shiftPlus mS =
          let
            fun shiftPlus' (M.Mnil, n) = n
              | shiftPlus' (M.Mapp (M.Marg (M.Plus, _), mS'), n) =
                  shiftPlus' (mS', n+1)
              | shiftPlus' (M.Mapp (M.Marg (M.Minus, _), mS'), n) =
                  shiftPlus' (mS', n)
          in
            shiftPlus' (mS, 0)
          end

        val n = shiftPlus mS
        val (F, F') = convertFor' (V, mS, I.id, I.Shift n, n)
      in
        F F'
      end


    (* convertFor L = F'

       Invariant:
       If   L is a list of type families
       then F' is the conjunction of the logical interpretation of each
            type family
     *)
    fun convertFor nil = raise Error "Empty theorem"
      | convertFor [a] = convertOneFor a
      | convertFor (a :: L) = T.And (convertOneFor a, convertFor L)

   (* here ends the preliminary stuff *)

    datatype MenuItem
    = Split     of Split.operator
    | Fill      of Fill.operator
    | Introduce of Introduce.operator
    | Fix       of FixedPoint.operator
    | Elim      of Elim.operator

    val Focus : (S.State list) ref = ref []

    val Menu : MenuItem list option ref = ref NONE


    fun SplittingToMenu (O, A) = Split O :: A

    fun initFocus () = (Focus := [])


    fun normalize () =
        (case (!Focus)
          of (S.State (W, Psi, P, F) :: Rest) =>
              (Focus := (S.State (W, Psi, T.derefPrg P, F) :: Rest))
           | _ => ())

    fun reset () =
        (initFocus ();
         Menu := NONE)

    fun format k =
        if k < 10 then (Int.toString k) ^ ".  "
        else (Int.toString k) ^ ". "

    fun menuToString () =
        let
          fun menuToString' (k, nil) = ""
            | menuToString' (k, Split O  :: M) =
              let
                val s = menuToString' (k+1, M)
              in
                 s ^ "\n  " ^ (format k) ^ (Split.menu O)
              end
            | menuToString' (k, Introduce O :: M) =
              let
                val s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Introduce.menu O)
              end
            | menuToString' (k, Fill O :: M) =
              let
                val s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Fill.menu O)
              end
            | menuToString' (k, Fix O :: M) =
              let
                val s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (FixedPoint.menu O)
              end
            | menuToString' (k, Elim O :: M) =
              let
                val s = menuToString' (k+1, M)
              in
                s ^ "\n  " ^ (format k) ^ (Elim.menu O)
              end
(*          | menuToString' (k, Inference O :: M,kOopt) =
              let
                val (kopt, s) = menuToString' (k+1, M, kOopt)
              in
                (kopt, s ^ "\n  " ^ (format k) ^ (Inference.menu O))
              end
*)      in
          case !Menu of
            NONE => raise Error "Menu is empty"
          | SOME M =>  menuToString' (1, M)
        end


    fun printStats () =
        let
          val nopen   = 0
          val nsolved = 0
        in
          (print "Statistics:\n\n";
           print ("Number of goals : " ^ (Int.toString (nopen + nsolved)) ^"\n");
           print ("     open goals : " ^ (Int.toString (nopen)) ^ "\n");
           print ("   solved goals : " ^ (Int.toString (nsolved)) ^ "\n"))
        end

    fun printmenu () =
        (case !Focus
           of [] => abort "QED"
            | (S.State (W, Psi, P, F) :: R) =>
                  (print ("\n=======================");
                   print ("\n= META THEOREM PROVER =\n");
                   print (TomegaPrint.ctxToString (Psi));
                   print ("\n-----------------------\n");
                   print (TomegaPrint.forToString (Psi, F));
                   print ("\n-----------------------\n");
                   print (TomegaPrint.prgToString (Psi, P));
                   print ("\n-----------------------");
                   print (menuToString ());
                   print ("\n=======================\n"))
            | (S.StateLF (X as I.EVar (r, G, V, Cs)) :: R) =>
                  (print ("\n=======================");
                   print ("\n=== THEOREM PROVER ====\n");
                   print (Print.ctxToString (I.Null, G));
                   print ("\n-----------------------\n");
                   print (Print.expToString (G, V));
                   print ("\n-----------------------\n");
                   print (Print.expToString (G, X));
                   print ("\n-----------------------");
                   print (menuToString ());
                   print ("\n=======================\n")))



    fun menu () =
        (case (!Focus)
           of [] => print "Please initialize first\n"
            | (S.State (W, Psi, P, F) :: _) =>
              let
                val Xs = S.collectT P
                val F1 = map (fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                             S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs
                val Ys = S.collectLF P
                val F2 = map (fn Y => S.FocusLF Y) Ys


                fun splitMenu [] = []
                  | splitMenu (operators :: l) = map Split operators @ splitMenu l

                val _ = Global.doubleCheck := true


                fun introMenu [] =  []
                  | introMenu ((SOME oper) :: l) = (Introduce oper) :: introMenu l
                  | introMenu (NONE :: l) = introMenu l

                val intro = introMenu (map Introduce.expand F1)


                val fill = foldr (fn (S, l) => l @ map (fn O => Fill O) (Fill.expand S)) nil F2

                fun elimMenu [] = []
                  | elimMenu (operators :: l) = map Elim operators @ elimMenu l

                val elim = elimMenu (map Elim.expand F1)

                val split = splitMenu (map Split.expand F1)
              in
                Menu := SOME (intro @ split @ fill @ elim)
              end
            | (S.StateLF Y :: _) =>
              let
                val Ys = Abstract.collectEVars (I.Null, (Y, I.id), nil)
                val F2 = map (fn Y => S.FocusLF Y) Ys
                val fill = foldr (fn (S, l) => l @ map (fn O => Fill O) (Fill.expand S)) nil F2
              in
                Menu := SOME (fill)
              end)


    fun select k =
        let
          fun select' (k, nil) = abort ("No such menu item")
            | select' (1, Split O :: _) =
                (Timers.time Timers.splitting Split.apply) O
            | select' (1, Introduce O :: _) =
                Introduce.apply O    (* no timer yet -- cs *)
            | select' (1, Elim O :: _) =
                Elim.apply O    (* no timer yet -- cs *)
            | select' (1, Fill O :: _) =
                (Timers.time Timers.filling Fill.apply) O
            | select' (k, _ :: M) = select' (k-1, M)
        in
          (case !Menu of
            NONE => raise Error "No menu defined"
          | SOME M => (select' (k, M); normalize (); menu (); printmenu())
             handle S.Error s => ())
        end


    fun init names =
        let
          val _ = TomegaPrint.evarReset()
          val cL = map (fn x => valOf (Names.constLookup (valOf (Names.stringToQid x)))) names
          val F = convertFor cL
          val Ws = map W.lookup cL
          fun select c = (Order.selLookup c handle _ => Order.Lex [])

          val TC = Tomega.transformTC (I.Null, F, map select cL)
          (* so far omitted:  make sure that all parts of the theorem are
             declared in the same world
          *)
          val (W :: _) = Ws
          val _ = Focus :=  [S.init (F, W)]
          val P = (case (!Focus)
                     of [] => abort "Initialization of proof goal failed\n"
                   | (S.State (W, Psi, P, F) :: _) => P)
          val Xs = S.collectT P
          val F = map (fn (T.EVar (Psi, r, F, TC, TCs, X)) => (Names.varReset I.Null;
                                                    S.Focus (T.EVar (TomegaPrint.nameCtx Psi, r, F, TC, TCs, X), W))) Xs
          val [Ofix] = map (fn f => (FixedPoint.expand (f, TC))) F
          val _ = FixedPoint.apply Ofix
          val _ = normalize ();
          val _ = menu ()
          val _ = printmenu ()
        in
          ()
        end


    (* focus n = ()

       Invariant:
       Let n be a string.
       Side effect: Focus on selected subgoal.
    *)
    fun focus n =
        (case (!Focus)
           of [] => print "Please initialize first\n"
            | (S.State (W, Psi, P, F) :: _) =>
              let
                fun findIEVar nil = raise Error ("cannot focus on " ^ n)
                  | findIEVar (Y :: Ys) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                       (Focus := (S.StateLF Y :: !Focus);
                        normalize ();
                        menu ();
                        printmenu ())
                    else findIEVar Ys
                fun findTEVar nil = findIEVar (S.collectLF P)
                  | findTEVar ((X as T.EVar (Psi, r, F, TC, TCs, Y)) :: Xs) =
                    if Names.evarName (T.coerceCtx Psi, Y) = n then
                      (Focus := (S.State (W, TomegaPrint.nameCtx Psi, X, F) :: !Focus);
                       normalize ();
                       menu ();
                       printmenu ())
                    else findTEVar Xs
              in
                findTEVar (S.collectT P)
              end
            | (S.StateLF (U) :: _) =>
              (* Invariant: U has already been printed, all EVars occuring
                 in U are already named.
              *)
              (case (Names.getEVarOpt n)
                 of NONE => raise Error ("cannot focus on " ^ n)
                  | SOME Y =>
                       (Focus := (S.StateLF Y :: !Focus);
                        normalize ();
                        menu ();
                        printmenu ())))


    fun return () =
      (case (!Focus)
        of [S] => if S.close S then print "[Q.E.D.]\n" else ()
         | (S :: Rest) => (Focus := Rest ; normalize (); menu (); printmenu ()))

  in
    val init = init
    val select = select
    val print = printmenu
    val stats = printStats
    val reset = reset
    val focus = focus
    val return = return
  end
end (* functor Interactive *)