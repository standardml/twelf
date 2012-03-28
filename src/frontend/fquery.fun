(* fquery: Executing logic programs via functional interpretation *)
(* Author: Carsten Schuermann *)

functor Fquery
  (structure Global : GLOBAL
   structure Names : NAMES
   structure ReconQuery : RECON_QUERY
   structure Timers : TIMERS
   structure Print : PRINT)
 : FQUERY =
struct
  structure ExtQuery = ReconQuery

  exception AbortQuery of string


  structure I = IntSyn
  structure T = Tomega
  structure W = WorldSyn
  structure P = Paths

  (* evarInstToString Xs = msg
     formats instantiated EVars as a substitution.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun evarInstToString (Xs) =
      if !Global.chatter >= 3
        then Print.evarInstToString (Xs)
      else ""

  (* expToString (G, U) = msg
     formats expression as a string.
     Abbreviate as empty string if chatter level is < 3.
  *)
  fun expToString GU =
      if !Global.chatter >= 3
        then Print.expToString GU
      else ""


  fun lower (0, G, V) = (G, V)
    | lower (n, G, I.Pi ((D, _), V)) = lower (n-1, I.Decl (G, D), V)

  fun run (quy, Paths.Loc (fileName, r)) =
      let
        (* optName = SOME(X) or NONE, Xs = free variables in query excluding X *)
        val (V, optName, Xs) = ReconQuery.queryToQuery(quy, Paths.Loc (fileName, r))
                                        (* times itself *)
        val _ = if !Global.chatter >= 3
                  then print ("%fquery")
                else ()
        val _ = if !Global.chatter >= 3
                  then print (" ")
                else ()
        val _ = if !Global.chatter >= 3
                  then print ((Timers.time Timers.printing expToString)
                              (IntSyn.Null, V) ^ ".\n")
                else ()

        val (k, V1)  = Abstract.abstractDecImp V
        val (G, V2) = lower (k, I.Null, V1)
                                        (* G |- V'' : type *)
        val a = I.targetFam V2
        val W = W.lookup a
        val V3 = Worldify.worldifyGoal (G, V2)
        val _ = TypeCheck.typeCheck (G, (V3, I.Uni I.Type))
        val P = Converter.convertGoal (T.embedCtx G, V3)
        val V = (Timers.time Timers.delphin Opsem.evalPrg) P
      in
        print ("Delphin: " ^ TomegaPrint.prgToString (I.Null, V) ^ "\n")
      end

end; (* functor Solve *)
