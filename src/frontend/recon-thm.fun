(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor ReconThm (structure Global : GLOBAL
                  (* structure IntSyn : INTSYN *)
                  structure Abstract : ABSTRACT
                  (*! sharing Abstract.IntSyn = IntSyn !*)
                  structure Constraints : CONSTRAINTS
                  structure Names : NAMES
                  (*! sharing Names.IntSyn = IntSyn !*)
                  (*! structure Paths' : PATHS !*)
                  structure ThmSyn': THMSYN
                    sharing ThmSyn'.Names = Names
                  structure ReconTerm': RECON_TERM
                  (*! sharing ReconTerm'.IntSyn = IntSyn !*)
                  (*! sharing ReconTerm'.Paths = Paths'  !*)
                  structure Print : PRINT
                  (*! sharing Print.IntSyn = IntSyn !*)
                    )
  : RECON_THM =
struct
  structure ThmSyn = ThmSyn'
  (*! structure Paths = Paths' !*)
  structure ExtSyn = ReconTerm'

  exception Error of string

  local
    structure M = ModeSyn
    structure I = IntSyn
    structure L = ThmSyn
    structure P = Paths
    structure T = ReconTerm'

    fun error (r, msg) = raise Error (P.wrap (r, msg))

    type order = ThmSyn.Order * Paths.region

    fun varg (r, L) = (ThmSyn.Varg L, r)

    fun lex (r0, L) =
        let
          fun lex' nil = (nil, r0)
            | lex' ((O, r) :: L) =
              let
                val (Os, r') = lex' L
              in
                (O :: Os, Paths.join (r, r'))
              end
          val (Os, r1) = lex' L
        in
          (ThmSyn.Lex Os, r1)
        end

    fun simul (r0, L) =
        let
          fun simul' nil = (nil, r0)
            | simul' ((O, r) :: L) =
              let
                val (Os, r') = simul' L
              in
                (O :: Os, Paths.join (r, r'))
              end
          val (Os, r1) = simul' L
        in
          (ThmSyn.Simul Os, r1)
        end

    type callpats = (ThmSyn.Callpats * Paths.region list)

    fun checkArgNumber (0, I.Uni (I.Type), nil, r) = ()
      | checkArgNumber (0, I.Pi (_, V2), arg::args, r) =
          checkArgNumber (0, V2, args, r)
      | checkArgNumber (0, I.Pi (_, V2), nil, r) =
          error (r, "Missing arguments in call pattern")
      | checkArgNumber (0, I.Uni (I.Type), arg::args, r) =
          error (r, "Extraneous arguments in call pattern")
      | checkArgNumber (i, I.Pi (_, V2), args, r) =
          checkArgNumber (i-1, V2, args, r)
      (* everything else should be impossible! *)

    fun checkCallPat (I.ConDec (_, _, i, I.Normal, V, I.Kind), P, r) =
          checkArgNumber (i, V, P, r)
      | checkCallPat (I.ConDec (a, _, _, I.Constraint _, _, _), P, r) =
          error (r, "Illegal constraint constant " ^ a ^ " in call pattern")
      | checkCallPat (I.ConDec (a, _, _, I.Foreign _, _, _), P, r) =
          error (r, "Illegal foreign constant " ^ a ^ " in call pattern")
      | checkCallPat (I.ConDec (a, _, _, _, _, I.Type), P, r) =
          error (r, "Constant " ^ a ^ " in call pattern not a type family")
      | checkCallPat (I.ConDef (a, _, _, _, _, _, _), P, r) =
          error (r, "Illegal defined constant " ^ a ^ " in call pattern")
      | checkCallPat (I.AbbrevDef (a, _, _, _, _, _), P, r) =
          error (r, "Illegal abbreviation " ^ a ^ " in call pattern")
      | checkCallPat (I.BlockDec (a, _, _, _), P, r) =
          error (r, "Illegal block identifier " ^ a ^ " in call pattern")
      | checkCallPat (I.SkoDec (a, _, _, _, _), P, r) =
          error (r, "Illegal Skolem constant " ^ a ^ " in call pattern")

    fun callpats L =
        let
          fun callpats' nil = (nil, nil)
            | callpats' ((name, P, r) :: L) =
              let
                val (cps, rs) = (callpats' L)
                val qid = Names.Qid (nil, name)
              in
                (* check whether they are families here? *)
                case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>
                       (checkCallPat (I.sgnLookup cid, P, r);
                        ((cid, P) :: cps, (r :: rs)))
              end
          val (cps, rs) = callpats' L
        in
          (ThmSyn.Callpats (cps), rs)
        end

    type tdecl = ThmSyn.TDecl * (Paths.region * Paths.region list)
    fun tdecl ((O, r), (C, rs)) = (ThmSyn.TDecl (O, C), (r, rs))
    fun tdeclTotDecl T  = T

    (* -bp *)
    (* predicate *)
    type predicate = ThmSyn.Predicate * Paths.region
    fun predicate ("LESS", r) = (ThmSyn.Less, r)
      | predicate ("LEQ", r) =  (ThmSyn.Leq, r)
      | predicate ("EQUAL", r) = (ThmSyn.Eq, r)

    (* reduces declaration *)
    type rdecl = ThmSyn.RDecl * (Paths.region * Paths.region list)
    fun rdecl ((P, r0), (O1,r1), (O2, r2), (C, rs)) =
        let
            val r = Paths.join (r1, r2)
        in
            (ThmSyn.RDecl (ThmSyn.RedOrder(P ,O1, O2), C), (Paths.join (r0, r), rs))
        end

    fun rdeclTorDecl T  = T

     (* tabled declaration *)
    type tableddecl = (ThmSyn.TabledDecl * Paths.region)
    fun tableddecl (name, r) =
        let
          val qid = Names.Qid (nil, name)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.TabledDecl cid, r)
        end


    fun tableddeclTotabledDecl T  = T

    (* keepTable declaration *)
    type keepTabledecl = (ThmSyn.KeepTableDecl * Paths.region)
    fun keepTabledecl (name, r) =
        let
          val qid = Names.Qid (nil, name)
        in
          (* check whether they are families here? *)
         case Names.constLookup qid
                  of NONE => error (r, "Undeclared identifier "
                                    ^ Names.qidToString (valOf (Names.constUndef qid))
                                    ^ " in call pattern")
                   | SOME cid =>    (ThmSyn.KeepTableDecl cid, r)
        end


    fun keepTabledeclToktDecl T  = T

    (* Theorem and prove declarations *)

    type prove = ThmSyn.PDecl * (Paths.region * Paths.region list)
    fun prove (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    fun proveToProve P = P

    type establish = ThmSyn.PDecl * (Paths.region * Paths.region list)
    fun establish (n, (td, rrs)) = (ThmSyn.PDecl (n, td), rrs)
    fun establishToEstablish P = P

    type assert = ThmSyn.Callpats * Paths.region list
    fun assert (cp, rs) = (cp, rs)
    fun assertToAssert P = P

    type decs = ExtSyn.dec I.Ctx
    val null = I.Null
    val decl = I.Decl

    type labeldec = decs * decs
    type thm = labeldec list * ExtSyn.dec I.Ctx * ModeSyn.Mode I.Ctx * int

    type theorem = thm -> thm
    type theoremdec = string * theorem

    fun dec (name, t) = (name, t)

    fun ctxAppend (G, I.Null) = G
      | ctxAppend (G, I.Decl (G', D)) = I.Decl (ctxAppend (G, G'), D)

    fun ctxMap f (I.Null) = I.Null
      | ctxMap f (I.Decl (G, D)) = I.Decl (ctxMap f G, f D)

    fun ctxBlockToString (G0, (G1, G2)) =
        let
          val _ = Names.varReset I.Null
          val G0' = Names.ctxName G0
          val G1' = Names.ctxLUName G1
          val G2' = Names.ctxLUName G2
        in
          Print.ctxToString (I.Null, G0') ^ "\n"
          ^ (case G1' of I.Null => "" | _ => "some " ^ Print.ctxToString (G0', G1') ^ "\n")
          ^ "pi " ^ Print.ctxToString (ctxAppend (G0', G1'), G2')
        end

    fun checkFreevars (I.Null, (G1, G2), r) = ()
      | checkFreevars (G0, (G1, G2), r) =
        let
          val _ = Names.varReset I.Null
          val G0' = Names.ctxName G0
          val G1' = Names.ctxLUName G1
          val G2' = Names.ctxLUName G2
        in
          error (r, "Free variables in context block after term reconstruction:\n"
                 ^ ctxBlockToString (G0', (G1', G2')))
        end

    fun abstractCtxPair (g1, g2) =
        let
          (* each block reconstructed independent of others *)
          val r = (case (T.ctxRegion g1, T.ctxRegion g2)
                     of (SOME r1, SOME r2) => Paths.join (r1, r2)
                      | (_, SOME r2) => r2)
          val T.JWithCtx (G1, T.JWithCtx (G2, _)) =
                T.recon (T.jwithctx (g1, T.jwithctx (g2, T.jnothing)))
          val (G0, [G1', G2']) =        (* closed nf *)
              Abstract.abstractCtxs [G1, G2]
              handle Constraints.Error (C)
              => error (r, "Constraints remain in context block after term reconstruction:\n"
                        ^ ctxBlockToString (I.Null, (G1, G2)) ^ "\n"
                        ^ Print.cnstrsToString C)
          val _ = checkFreevars (G0, (G1', G2'), r)
        in
          (G1', G2')
        end

    fun top (GBs, g, M, k) = (GBs, g, M, k)

    fun exists (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fn _ => M.Minus) g'), k)

    fun forall (g', t) (GBs, g, M, k) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fn _ => M.Plus) g'), k)

    fun forallStar (g', t) (GBs, g, M, _) =
          t (GBs, ctxAppend (g, g'),
             ctxAppend (M, ctxMap (fn _ => M.Plus) g'), I.ctxLength g')

    fun forallG (gbs, t:thm->thm) (_:thm):thm =
          t (gbs, I.Null, I.Null, 0)

    fun theoremToTheorem t =
        let
          val (gbs, g, M, k) = t (nil, I.Null, I.Null, 0)
          val _ = Names.varReset IntSyn.Null
          val GBs = List.map abstractCtxPair gbs
          val T.JWithCtx (G, _) = T.recon (T.jwithctx (g, T.jnothing))
        in
          L.ThDecl (GBs, G, M, k)
        end

    fun theoremDecToTheoremDec (name, t) =
          (name, theoremToTheorem t)

    (* World checker *)

    fun abstractWDecl W =
        let
          val W' = List.map Names.Qid W
        in
          W'
        end

    type wdecl =  ThmSyn.WDecl * Paths.region list
    fun wdecl (W, (cp, rs)) = (ThmSyn.WDecl (abstractWDecl W, cp), rs)
    fun wdeclTowDecl T = T

  in
    (* avoid this re-copying? -fp *)
    type order = order
    val varg = varg
    val lex = lex
    val simul = simul

    type callpats = callpats
    val callpats = callpats

    type tdecl = tdecl
    val tdecl = tdecl

    (* -bp *)
    type predicate = predicate
    val predicate = predicate

    (* -bp *)
    type rdecl = rdecl
    val rdecl = rdecl

    type tableddecl = tableddecl
    val tableddecl = tableddecl

    type keepTabledecl = keepTabledecl
    val keepTabledecl = keepTabledecl

    type prove = prove
    val prove = prove

    type establish = establish
    val establish = establish

    type assert = assert
    val assert = assert

    val tdeclTotDecl = tdeclTotDecl
    val rdeclTorDecl = rdeclTorDecl

    val tableddeclTotabledDecl = tableddeclTotabledDecl
    val keepTabledeclToktDecl = keepTabledeclToktDecl

    val proveToProve = proveToProve
    val establishToEstablish = establishToEstablish
    val assertToAssert = assertToAssert

    type decs = decs
    val null = null
    val decl = decl

    type theorem = theorem
    val top = top
    val forallStar = forallStar
    val forall = forall
    val exists = exists
    val forallG = forallG
    val theoremToTheorem = theoremToTheorem

    type theoremdec = theoremdec
    val dec = dec
    val theoremDecToTheoremDec = theoremDecToTheoremDec

    type wdecl = wdecl
    val wdeclTowDecl = wdeclTowDecl
    val wdecl = wdecl
  end (* local *)
end (* functor ReconThm *)
