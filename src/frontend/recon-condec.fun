(* Reconstruct signature entries *)
(* Author: Frank Pfenning *)
(* Modified: Roberto Virga, Jeff Polakow *)

functor ReconConDec (structure Global : GLOBAL
                     (*! structure IntSyn' : INTSYN !*)
                     structure Names : NAMES
                     (*! sharing Names.IntSyn = IntSyn' !*)
                     structure Abstract : ABSTRACT
                     (*! sharing Abstract.IntSyn = IntSyn' !*)
                     (*! structure Paths' : PATHS !*)
                     structure ReconTerm' : RECON_TERM
                     (*! sharing ReconTerm'.IntSyn = IntSyn' !*)
                     (*! sharing ReconTerm'.Paths = Paths' !*)
                     structure Constraints : CONSTRAINTS
                     (*! sharing Constraints.IntSyn = IntSyn' !*)
                     structure Strict : STRICT
                     (*! sharing Strict.IntSyn = IntSyn' !*)
                     (*! sharing Strict.Paths = Paths' !*)
                     structure TypeCheck : TYPECHECK
                     (*! sharing TypeCheck.IntSyn = IntSyn' !*)
                     structure Timers : TIMERS
                     structure Print : PRINT
                     (*! sharing Print.IntSyn = IntSyn' !*)
                     structure Msg : MSG
                       )
  : RECON_CONDEC =
struct
  (*! structure IntSyn = IntSyn' !*)
  (*! structure Paths = Paths' !*)
  structure ExtSyn = ReconTerm'

  exception Error of string

  (* error (r, msg) raises a syntax error within region r with text msg *)
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  type name = string

  (* Constant declarations *)
  datatype condec =
      condec of name * ExtSyn.term
    | condef of name option * ExtSyn.term * ExtSyn.term option
    | blockdef of string *  (string list * string) list
    | blockdec of name * ExtSyn.dec list * ExtSyn.dec list

  (* condecToConDec (condec, r) = (SOME(cd), SOME(ocd))
     if condec is a named constant declaration with occurrence tree ocd,
     NONE if name or occurrence tree is missing

     Free variables in condec are interpreted universally (as FVars)
     then abstracted as implicit parameters.

     Only works properly when the declaration contains no EVars.
  *)
  (* should printing of result be moved to frontend? *)
  (* Wed May 20 08:08:50 1998 -fp *)
  fun condecToConDec (condec(name, tm), Paths.Loc (fileName, r), abbFlag) =
      let
        val _ = Names.varReset IntSyn.Null
        val _ = ExtSyn.resetErrors fileName
        val ExtSyn.JClass ((V, oc), L) =
              (Timers.time Timers.recon ExtSyn.recon) (ExtSyn.jclass tm)
        val _ = ExtSyn.checkErrors (r)
        val (i, V') = (Timers.time Timers.abstract Abstract.abstractDecImp) V
                        handle Abstract.Error (msg)
                               => raise Abstract.Error (Paths.wrap (r, msg))
        val cd = Names.nameConDec (IntSyn.ConDec (name, NONE, i, IntSyn.Normal, V', L))
        val ocd = Paths.dec (i, oc)
        val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        val _ = if !Global.doubleCheck
                  then (Timers.time Timers.checking TypeCheck.check) (V', IntSyn.Uni L)
                else ()
      in
        (SOME(cd), SOME(ocd))
      end
    | condecToConDec (condef(optName, tm1, tm2Opt), Paths.Loc (fileName, r), abbFlag) =
      let
        val _ = Names.varReset IntSyn.Null
        val _ = ExtSyn.resetErrors fileName
        val f = (case tm2Opt
                   of NONE => ExtSyn.jterm tm1
                    | SOME tm2 => ExtSyn.jof (tm1, tm2))
        val f' = (Timers.time Timers.recon ExtSyn.recon) f
        val ((U, oc1), (V, oc2Opt), L) =
            (case f'
               of ExtSyn.JTerm ((U, oc1), V, L) =>
                    ((U, oc1), (V, NONE), L)
                | ExtSyn.JOf ((U, oc1), (V, oc2), L) =>
                    ((U, oc1), (V, SOME oc2), L))
        val _ = ExtSyn.checkErrors (r)
        val (i, (U'', V'')) =
                (Timers.time Timers.abstract Abstract.abstractDef) (U, V)
                handle Abstract.Error (msg)
                          => raise Abstract.Error (Paths.wrap (r, msg))
        val name = case optName of NONE => "_" | SOME(name) => name
        val ocd = Paths.def (i, oc1, oc2Opt)
        val cd = if abbFlag then Names.nameConDec (IntSyn.AbbrevDef (name, NONE, i, U'', V'', L))
                 else (Strict.check ((U'', V''), SOME(ocd));
                       (* stricter checking of types according to Chris Richards Fri Jul  2 16:33:46 2004 -fp *)
                       (* (case optName of NONE => () | _ => Strict.checkType ((i, V''), SOME(ocd))); *)
                       (Names.nameConDec (IntSyn.ConDef (name, NONE, i, U'', V'', L,
                                                         IntSyn.ancestor U''))))

        val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) cd ^ "\n")
                else ()
        val _ = if !Global.doubleCheck
                  then ((Timers.time Timers.checking TypeCheck.check) (V'', IntSyn.Uni L);
                        (Timers.time Timers.checking TypeCheck.check) (U'', V''))
                else ()
        val optConDec = case optName of NONE => NONE | SOME _ => SOME (cd)
      in
        (optConDec, SOME(ocd))
      end
    | condecToConDec (blockdec (name, Lsome, Lblock), Paths.Loc (fileName, r), abbFlag) =
      let
        fun makectx nil = IntSyn.Null
          | makectx (D :: L) = IntSyn.Decl (makectx L, D)
        fun ctxToList (IntSyn.Null, acc) = acc
          | ctxToList (IntSyn.Decl (G, D), acc) = ctxToList (G, D :: acc)
        fun ctxAppend (G, IntSyn.Null) = G
          | ctxAppend (G, IntSyn.Decl (G', D)) = IntSyn.Decl (ctxAppend (G, G'), D)
        fun ctxBlockToString (G0, (G1, G2)) =
            let
              val _ = Names.varReset IntSyn.Null
              val G0' = Names.ctxName G0
              val G1' = Names.ctxLUName G1
              val G2' = Names.ctxLUName G2
            in
              Print.ctxToString (IntSyn.Null, G0') ^ "\n"
              ^ (case G1' of IntSyn.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
              ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
            end
        fun checkFreevars (IntSyn.Null, (G1, G2), r) = ()
          | checkFreevars (G0, (G1, G2), r) =
            let
              val _ = Names.varReset IntSyn.Null
              val G0' = Names.ctxName G0
              val G1' = Names.ctxLUName G1
              val G2' = Names.ctxLUName G2
            in
              error (r, "Free variables in context block after term reconstruction:\n"
                     ^ ctxBlockToString (G0', (G1', G2')))
            end

        val (gsome, gblock) = (makectx Lsome, makectx Lblock)

        val r' = (case (ExtSyn.ctxRegion gsome, ExtSyn.ctxRegion gblock)
                    of (SOME r1, SOME r2) => Paths.join (r1, r2)
                     | (_, SOME r2) => r2)

        val _ = Names.varReset IntSyn.Null
        val _ = ExtSyn.resetErrors fileName
        val j = ExtSyn.jwithctx (gsome,
                  ExtSyn.jwithctx (gblock, ExtSyn.jnothing))
        val ExtSyn.JWithCtx (Gsome, ExtSyn.JWithCtx (Gblock, _)) =
              (Timers.time Timers.recon ExtSyn.recon) j
        val _ = ExtSyn.checkErrors (r)
        val (G0, [Gsome', Gblock']) =   (* closed nf *)
          Abstract.abstractCtxs [Gsome, Gblock]
          handle Constraints.Error (C)
          => (raise error (r', "Constraints remain in context block after term reconstruction:\n"
                    ^ ctxBlockToString (IntSyn.Null, (Gsome, Gblock)) ^ "\n"
                    ^ Print.cnstrsToString C))
        val _ = checkFreevars (G0, (Gsome', Gblock'), r')
        val bd = IntSyn.BlockDec (name, NONE, Gsome', ctxToList (Gblock', nil))
        val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else ()

      in
        (SOME bd, NONE)
      end
    | condecToConDec (blockdef (name, W), Paths.Loc (fileName, r), abbFlag) =
      let
        val W' = List.map Names.Qid W
        val W'' = (List.map (fn qid => case Names.constLookup qid
                                    of NONE => raise Names.Error ("Undeclared label "
                                         ^ Names.qidToString (valOf (Names.constUndef qid))
                                         ^ ".")
                                     | SOME cid => cid)
              W')
        val bd = IntSyn.BlockDef (name, NONE, W'')
        val _ = if !Global.chatter >= 3
                  then Msg.message ((Timers.time Timers.printing Print.conDecToString) bd ^ "\n")
                else ()
      in
        (SOME bd, NONE)
      end

  fun internalInst _ = raise Match
  fun externalInst _ = raise Match

end (* functor ReconConDec *)
