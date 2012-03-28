(* Strategy *)
(* Author: Carsten Schuermann *)

functor StrategyFRS (structure MetaGlobal : METAGLOBAL
                     structure MetaSyn' : METASYN
                     structure Filling : FILLING
                     sharing Filling.MetaSyn = MetaSyn'
                     structure Splitting : SPLITTING
                     sharing Splitting.MetaSyn = MetaSyn'
                     structure Recursion : RECURSION
                     sharing Recursion.MetaSyn = MetaSyn'
                     structure Lemma : LEMMA
                     sharing Lemma.MetaSyn = MetaSyn'
                     structure Qed : QED
                     sharing Qed.MetaSyn = MetaSyn'
                     structure MetaPrint : METAPRINT
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     structure Timers : TIMERS)
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  local

    structure M = MetaSyn

    fun printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: FRS\n"
        else ()

    fun printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    fun printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    fun printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    fun printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    fun printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    fun printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun findMin nil = NONE
      | findMin (O :: L) =
        let
          fun findMin' (nil, k, result) = result
            | findMin' (O' :: L', k ,result)=
                let
                  val k' = Splitting.index O'
                in
                  if Splitting.index O' < k then findMin' (L', k', SOME O')
                  else findMin' (L', k, result)
                end
        in
          findMin' (L, Splitting.index O, SOME O)
        end

    (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
    fun split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S)
          of NONE => fill (givenStates, (S :: openStates, solvedStates))
           | SOME splitOp =>
             let
               val _ = printSplitting ()
               val SL = (Timers.time Timers.splitting Splitting.apply) splitOp
               val _ = printCloseBracket ()
             in
               (fill (SL @ givenStates, os)
                handle Splitting.Error _ => fill (givenStates, (S :: openStates, solvedStates)))
             end

    and recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => split (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               val _ = printRecursion ()
               val S' = (Timers.time Timers.recursion Recursion.apply) recursionOp
               val _ = printCloseBracket ()
             in
               (fill (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => split (S :: givenStates, os))
             end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
      let
        fun fillOp () =
          case (Timers.time Timers.filling Filling.expand) S
            of (_, fillingOp) =>
              (let
                 val _ = printFilling ()
                 val [S'] = (Timers.time Timers.filling Filling.apply) fillingOp
                 val _ = printCloseBracket ()
               in
                 if Qed.subgoal S'
                   then (printFinish S'; fill (givenStates, (openStates, S' :: solvedStates)))
                 else fill (S' :: givenStates, os)
               end
                 handle Filling.Error _ => recurse (S :: givenStates, os))
      in
        (TimeLimit.timeLimit (!Global.timeLimit) fillOp ())
        handle TimeLimit.TimeOut =>
          (print "\n----------- TIME OUT ---------------\n" ; raise Filling.TimeOut)

      end

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    fun run givenStates =
        let
          val _ = printInit ()
          val os = fill (givenStates, (nil, nil))
          val _ = case os
                    of (nil, _) => printQed ()
                     | _ => ()
        in
          os
        end
  in
    val run = run
  end (* local *)
end;  (* functor StrategyFRS *)



functor StrategyRFS (structure MetaGlobal : METAGLOBAL
                     structure MetaSyn' : METASYN
                     structure Filling : FILLING
                     sharing Filling.MetaSyn = MetaSyn'
                     structure Splitting : SPLITTING
                     sharing Splitting.MetaSyn = MetaSyn'
                     structure Recursion : RECURSION
                     sharing Recursion.MetaSyn = MetaSyn'
                     structure Lemma : LEMMA
                     sharing Lemma.MetaSyn = MetaSyn'
                     structure Qed : QED
                     sharing Qed.MetaSyn = MetaSyn'
                     structure MetaPrint : METAPRINT
                     sharing MetaPrint.MetaSyn = MetaSyn'
                     structure Timers : TIMERS)
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  local

    structure M = MetaSyn

    fun printInit () =
        if !Global.chatter > 3 then print "Strategy 1.0: RFS\n"
        else ()

    fun printFinish (M.State (name, _, _)) =
        if !Global.chatter > 5 then print ("[Finished: " ^ name ^ "]\n")
        else if !Global.chatter> 4 then print ("[" ^ name ^ "]\n")
             else if !Global.chatter> 3 then print ("[" ^ name ^ "]")
                  else ()

    fun printFilling () =
        if !Global.chatter > 5 then print ("[Filling ... ")
        else if !Global.chatter> 4 then print ("F")
             else  ()

    fun printRecursion () =
        if !Global.chatter > 5 then print ("[Recursion ...")
        else if !Global.chatter> 4 then print ("R")
             else ()

    fun printSplitting () =
        if !Global.chatter > 5 then print ("[Splitting ...")
        else if !Global.chatter> 4 then print ("S")
             else ()

    fun printCloseBracket () =
        if !Global.chatter > 5 then print ("]\n")
        else ()

    fun printQed () =
        if !Global.chatter > 3 then print ("[QED]\n")
        else ()

    (* findMin L = Sopt

       Invariant:

       If   L be a set of splitting operators
       then Sopt = NONE if L = []
       else Sopt = SOME S, s.t. index S is minimal among all elements in L
    *)
    fun findMin nil = NONE
      | findMin (O :: L) =
          let
            fun findMin' (nil, k, result) = result
              | findMin' (O' :: L', k ,result)=
                  let
                    val k' = Splitting.index O'
                  in
                    if Splitting.index O' < k then findMin' (L', k', SOME O')
                    else findMin' (L', k, result)
                  end
          in
            findMin' (L, Splitting.index O, SOME O)
          end

    (* split   (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       recurse (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')
       fill    (givenStates, (openStates, solvedStates)) = (openStates', solvedStates')

       Invariant:
       openStates' extends openStates and
         contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' extends solvedStates and
         contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
    *)
    fun split (S :: givenStates, os as (openStates, solvedStates)) =
        case findMin ((Timers.time Timers.splitting Splitting.expand) S) of
          NONE => recurse (givenStates, (S :: openStates, solvedStates))
        | SOME splitOp =>
            let
              val _ = printSplitting ()
              val SL = (Timers.time Timers.splitting Splitting.apply) splitOp
              val _ = printCloseBracket ()
            in
              (recurse (SL @ givenStates, os)
               handle Splitting.Error _ => recurse (givenStates, (S :: openStates, solvedStates)))
            end

    and fill (nil, os) = os
      | fill (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.filling Filling.expand) S
          of (_, fillingOp) =>
             (let
                val _ = printFilling ()
                val [S'] = (Timers.time Timers.filling Filling.apply) fillingOp
                val _ = printCloseBracket ()
              in
                if Qed.subgoal S' then
                  (printFinish S'; recurse (givenStates, (openStates, S' :: solvedStates)))
                else fill (S' :: givenStates, os)
              end
                handle Filling.Error _ => split (S :: givenStates, os))

    and recurse (nil, os) = os
      | recurse (S :: givenStates, os as (openStates, solvedStates)) =
        case (Timers.time Timers.recursion Recursion.expandEager) S
          of nil => fill (S :: givenStates, os)
           | (recursionOp :: _) =>
             let
               val _ = printRecursion ()
               val S' = (Timers.time Timers.recursion Recursion.apply) recursionOp
               val _ = printCloseBracket ()
             in
               (recurse (S' :: givenStates, (openStates, solvedStates))
                handle Recursion.Error _ => fill (S :: givenStates, os))
             end

    (* run givenStates = (openStates', solvedStates')

       Invariant:
       openStates' contains the states resulting from givenStates which cannot be
         solved using Filling, Recursion, and Splitting
       solvedStates' contains the states resulting from givenStates which can be
         solved using Filling, Recursion, and Splitting
     *)
    fun run givenStates =
        let
          val _ = printInit ()
          val os = recurse (givenStates, (nil, nil))
          val _ = case os
                    of (nil, _) => printQed ()
                     | _ => ()
        in
          os
        end
  in
    val run = run
  end (* local *)
end;  (* functor StrategyRFS *)



functor Strategy (structure MetaGlobal : METAGLOBAL
                  structure MetaSyn' : METASYN
                  structure StrategyFRS : STRATEGY
                  sharing StrategyFRS.MetaSyn = MetaSyn'
                  structure StrategyRFS : STRATEGY
                  sharing StrategyRFS.MetaSyn = MetaSyn')
  : STRATEGY =
struct

  structure MetaSyn = MetaSyn'

  fun run SL =
      case !MetaGlobal.strategy
        of MetaGlobal.RFS => StrategyRFS.run SL
         | MetaGlobal.FRS => StrategyFRS.run SL

end; (* functor Strategy *)
