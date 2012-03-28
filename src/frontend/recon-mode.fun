(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ReconMode (structure Global : GLOBAL
                   (*! structure ModeSyn' : MODESYN !*)
                   structure Whnf : WHNF
                   (*! sharing Whnf.IntSyn = ModeSyn'.IntSyn !*)
                   (*! structure Paths' : PATHS !*)
                   structure Names : NAMES
                   (*! sharing Names.IntSyn = ModeSyn'.IntSyn !*)
                   structure ModePrint : MODEPRINT
                   (*! sharing ModePrint.ModeSyn = ModeSyn' !*)
                   structure ModeDec : MODEDEC

                   structure ReconTerm' : RECON_TERM
                   (*! sharing ReconTerm'.IntSyn = ModeSyn'.IntSyn !*)
                   (*! sharing ReconTerm'.Paths = Paths' !*)
                       )
  : RECON_MODE =
struct
  (*! structure ModeSyn = ModeSyn' !*)
  structure ExtSyn = ReconTerm'
  (*! structure Paths = Paths' !*)

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  local
    structure M = ModeSyn
    structure I = IntSyn
    structure T = ExtSyn
    structure P = Paths

    type mode = M.Mode * P.region

    fun plus r = (M.Plus, r)
    fun star r = (M.Star, r)
    fun minus r = (M.Minus, r)
    fun minus1 r = (M.Minus1, r)

    type modedec = (I.cid * M.ModeSpine) * P.region

    structure Short =
    struct
      type mterm = (I.cid * M.ModeSpine) * P.region
      type mspine = M.ModeSpine * P.region

      fun mnil r = (M.Mnil, r)
      fun mapp (((m, r1), name), (mS, r2)) = (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))
      fun mroot (ids, id, r1, (mS, r2)) =
          let
            val r = P.join (r1, r2)
            val qid = Names.Qid (ids, id)
          in
            case Names.constLookup qid
              of NONE => error (r, "Undeclared identifier "
                                ^ Names.qidToString (valOf (Names.constUndef qid))
                                ^ " in mode declaration")
               | SOME cid => ((cid, ModeDec.shortToFull (cid, mS, r)), r)
          end

      fun toModedec nmS = nmS
    end  (* structure Short *)

    structure Full =
    struct
      type mterm = T.dec I.Ctx * M.Mode I.Ctx
                     -> (I.cid * M.ModeSpine) * P.region

      fun mpi ((m, _), d, t) (g, D) =
            t (I.Decl (g, d), I.Decl (D, m))

      fun mroot (tm, r) (g, D) =
          let
            val T.JWithCtx (G, T.JOf ((V, _), _, _)) =
                  T.recon (T.jwithctx (g, T.jof (tm, T.typ (r))))
            val _ = T.checkErrors (r)

            (* convert term spine to mode spine *)
            (* Each argument must be contractible to variable *)
            fun convertSpine (I.Nil) = M.Mnil
              | convertSpine (I.App (U, S)) =
                let
                  val k = Whnf.etaContract U
                          handle Whnf.Eta =>
                            error (r, "Argument " ^
                                      (Print.expToString(G, U)) ^
                                      " not a variable")
                                      (* print U? -fp *) (* yes, print U. -gaw *)
                  val I.Dec (name, _) = I.ctxLookup (G, k)
                  val mode = I.ctxLookup (D, k)
                in
                  M.Mapp (M.Marg (mode, name), convertSpine S)
                end

            (* convert root expression to head constant and mode spine *)
            fun convertExp (I.Root (I.Const (a), S)) =
                  (a, convertSpine S)
              | convertExp (I.Root (I.Def (d), S))  =
                  (* error is signalled later in ModeDec.checkFull *)
                  (d, convertSpine S)
              | convertExp _ =
                  error (r, "Call pattern not an atomic type")
              (* convertExp (I.Root (I.Skonst _, S)) can't occur *)

            val (a, mS) = convertExp (Whnf.normalize (V, I.id))
          in
            (ModeDec.checkFull (a, mS, r);  ((a, mS), r))
          end

      fun toModedec t =
          let
            val _ = Names.varReset I.Null
            val t' = t (I.Null, I.Null)
          in
            t'
          end

    end  (* structure Full *)

    fun modeToMode (m, r) = (m, r)

  in
    type mode = mode
    val plus = plus
    val star = star
    val minus = minus
    val minus1 = minus1

    type modedec = modedec

    structure Short = Short
    structure Full = Full

    val modeToMode = modeToMode
  end   (* local ... *)
end;  (* functor ReconMode *)
