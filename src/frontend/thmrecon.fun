(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)
(* Modified: Brigitte Pientka *)

functor ThmRecon (structure Global : GLOBAL
		  structure IntSyn : INTSYN
                  structure Abstract : ABSTRACT
		    sharing Abstract.IntSyn = IntSyn
		  structure Constraints : CONSTRAINTS
		    sharing Constraints.IntSyn = IntSyn
		  structure ModeSyn : MODESYN
		    sharing ModeSyn.IntSyn = IntSyn
		  structure ThmSyn': THMSYN
		    sharing ThmSyn'.ModeSyn = ModeSyn
		    sharing ThmSyn'.ModeSyn = ModeSyn
		  structure Paths' : PATHS
		  structure TpRecon': TP_RECON
		    sharing TpRecon'.IntSyn = IntSyn
		    sharing TpRecon'.Paths = Paths' 
		  structure Names : NAMES
		    sharing Names.IntSyn = IntSyn
		  structure Print : PRINT
		    sharing Print.IntSyn = IntSyn)
  : THM_RECON =
struct
  structure ThmSyn = ThmSyn'
  structure Paths = Paths'
  structure ExtSyn = TpRecon'

  exception Error of string

  local
    structure M = ModeSyn
    structure I = ModeSyn.IntSyn
    structure L = ThmSyn
    structure P = Paths
    structure T = TpRecon'

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

    fun checkCallPat (I.ConDec (_, i, I.Normal, V, I.Kind), P, r) =
          checkArgNumber (i, V, P, r)
      | checkCallPat (I.ConDec (a, _, I.Constraint _, _, _), P, r) =
	  error (r, "Illegal constraint constant " ^ a ^ " in call pattern")
      | checkCallPat (I.ConDec (a, _, I.Foreign _, _, _), P, r) =
          error (r, "Illegal foreign constant " ^ a ^ " in call pattern")
      | checkCallPat (I.ConDec (a, _, _, _, I.Type), P, r) =
	  error (r, "Constant " ^ a ^ " in call pattern not a type family")
      | checkCallPat (I.ConDef (a, _, _, _, _), P, r) =
          error (r, "Illegal defined constant " ^ a ^ " in call pattern")
      | checkCallPat (I.AbbrevDef (a, _, _, _, _), P, r) =
	  error (r, "Illegal abbreviation " ^ a ^ " in call pattern")
      | checkCallPat (I.SkoDec (a, _, _, _), P, r) =
	  error (r, "Illegal Skolem constant " ^ a ^ " in call pattern")

    fun callpats L = 
        let 
	  fun callpats' nil = (nil, nil)
	    | callpats' ((name, P, r) :: L) =  
	      let 
		val (cps, rs) =  (callpats' L)
	      in
		(* check whether they are families here? *)
		case Names.nameLookup name
		  of NONE => error (r, "Type family " ^ name ^ " not defined")
		   | SOME cid => 
		     ( checkCallPat (I.sgnLookup cid, P, r);
		       ((cid, P) :: cps, (r :: rs)) )
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

    type decs = (ExtSyn.dec * P.region) I.Ctx
    val null = I.Null
    val decl = I.Decl

    type labeldec = I.dctx * I.dctx
    type thm = labeldec list * I.dctx * ModeSyn.Mode I.Ctx

    type theorem2 = thm -> thm
    type theorem = T.approxCtx * int -> T.approxCtx * int * Paths.region * theorem2
    type theoremdec = string * theorem
    (* implicit arguments, Type, Modevector *)

    fun join (NONE, r) = SOME(r)
      | join (SOME(r1), r2) = SOME(P.join (r1, r2))

    fun ctxRegion (I.Null) = NONE
      | ctxRegion (I.Decl (g, (d, r))) = join (ctxRegion g, r)

    fun ctxAppend (G, I.Null) = G
      | ctxAppend (G, I.Decl (G', D)) = I.Decl (ctxAppend (G, G'), D)

    fun ctxBlockToString (G0, (G1, G2)) =
        let
	  val _ = Names.varReset ()
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
	  val _ = Names.varReset ()
	  val G0' = Names.ctxName G0
	  val G1' = Names.ctxLUName G1
	  val G2' = Names.ctxLUName G2
	in
	  error (r, "Free variables in context block after term reconstruction:\n"
		 ^ ctxBlockToString (G0', (G1', G2')))
	end

    (* recon (GBs, G1, M, G2, k, mode) = (GBs, G', M', k')
     
       Invariant:  
       If   G1 |- M   (where the k-prefix of G1 are implicit parameters)
       and  G1 |- G2 ctx
       and  mode is a mode
       then G' = G1, G2 (where the k'-prefix of G' are implicit parameters)
       and  M' = M, mode ... mode   (|G2| times)
       
    *)
    fun recon (GBs, G, M, I.Null, _) = (GBs, G, M)
      | recon (GBs, G, M, I.Decl (ctx, (Da, r)), mode) =
	let 
	  val (GBs', G', M') = recon (GBs, G, M, ctx, mode)
	  val D = T.approxDecToDec (G', Da, r)
	in
	  (GBs', I.Decl (G', D), I.Decl (M', mode))
	end

    fun reconCtx (G, I.Null) = (G, I.Null)
      | reconCtx (G, I.Decl (ctx, (d, r))) =
        let
	  val (G', G'') = reconCtx (G, ctx)
	  val D = T.decToApproxDec (G', d)
	in
          (I.Decl (G', D), I.Decl (G'', (D, r)))
	end

    fun reconCtx2 (G1, I.Null) = (G1, I.Null)
      | reconCtx2 (G1, I.Decl (ctx, (Da, r))) =
        let
          val (G', G'') = reconCtx2 (G1, ctx)
          val D = T.approxDecToDec (G', Da, r)
        in
          (I.Decl (G', D), I.Decl (G'', D))
        end

    fun reconCtxPair (ctxSome, ctxPi) =
        let
	  val (Ga1, Ga2) = reconCtx (I.Null, ctxSome)
	  val (_, Ga3) = reconCtx (Ga1, ctxPi)
	in
	  (Ga2, Ga3)
	end

    fun reconCtxPair2 (ctxSome, ctxPi) =
        let
          val (_, G1) = reconCtx2 (I.Null, ctxSome)
          val (_, G2) = reconCtx2 (G1, ctxPi)
        in
          (G1, G2)
        end

    fun abstractCtxPair2 (Ga1, Ga2) =	(* (Ga1,Ga2) already approx checked *)
        let
	  val r1Opt = ctxRegion Ga1
	  val SOME(r2) = ctxRegion Ga2	(* Ga2 cannot be empty *)
	  val SOME(r) = join (r1Opt, r2)
	  (* val (G1', G2') = reconCtxPair (Ga1, Ga2) *) (* approx *)
	  val (G1', G2') = reconCtxPair2 (Ga1, Ga2) (* accurate *)
	  val (G0, [G1'', G2'']) =	(* closed nf *)
	      Abstract.abstractCtxs [G1', G2'] 
	      handle Constraints.Error (C)
	      => error (r, "Constraints remain in context block after term reconstruction:\n"
			^ ctxBlockToString (I.Null, (G1', G2')) ^ "\n"
			^ Print.cnstrsToString C)
	  val _ = checkFreevars (G0, (G1'', G2''), r)
	in
	  (G1'', G2'')
	end 

    fun top2 (GBs, G, M) = (GBs, G, M)
    fun top r (Ga, k) = (Ga, k, r, top2)
    fun exists2 (Ga, t) (GBs, G, M) =
          t (recon (GBs, G, M, Ga, M.Minus))
    fun exists (g, (r, t)) (Ga, k) =
        let
          val (Ga1, Ga2) = reconCtx (Ga, g)
          val (Ga', k', r', t') = t (Ga1, k)
        in
          (Ga', k', P.join (r, r'), exists2 (Ga2, t'))
        end
    fun forall2 (ga, t) (GBs, G, M) =
          t (recon (GBs, G, M, ga, M.Plus))
    fun forall (g, (r, t)) (Ga, k) =
        let
          val (Ga1, Ga2) = reconCtx (Ga, g)
          val (Ga', k', r', t') = t (Ga1, k)
        in
          (Ga', k', P.join (r, r'), forall2 (Ga2, t'))
        end
    fun forallStar2 (ga, t) (GBs, G, M) =
          t (recon (GBs, G, M, ga, M.Plus))
    fun forallStar (g, (r, t)) (Ga, k) =
        let
          val (Ga1, Ga2) = reconCtx (Ga, g)
          val (Ga', k', r', t') = t (Ga1, I.ctxLength g)
        in
          (Ga', k', P.join (r, r'), forallStar2 (Ga2, t'))
        end
    fun forallG2 (GBas, t) (_, G, M) =
        let
          val GBs = List.map abstractCtxPair2 GBas
        in
          t (GBs, G, M)
        end
    fun forallG (gbs, (r, t)) (Ga, k) =
        let
          val GBas = List.map reconCtxPair gbs
          val (Ga', k', r', t') = t (Ga, k)
        in
          (Ga', k', P.join (r, r'), forallG2 (GBas, t'))
        end

    fun dec (name, t) = (name, t)

    fun theoremToTheorem t = 
        let
	  val _ = Names.varReset ()
          val (_, k, r', t') = t (I.Null, 0)
	  val (GBs, G, M) = t' (nil, I.Null, I.Null)
	in
	  (L.ThDecl (GBs, G, M, k), r')
	end

    fun theoremDecToTheoremDec (name, t) =
        let 
	  val (td', r') = theoremToTheorem t
	in
          ((name, td'), r')
	end

    (* World checker *)

    fun abstractWDecl W =
        let
	  val W' = List.map reconCtxPair W
	  val W'' = List.map abstractCtxPair2 W'
	in
	  W''
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

    type prove = prove
    val prove = prove

    type establish = establish
    val establish = establish

    type assert = assert
    val assert = assert

    val tdeclTotDecl = tdeclTotDecl
    val rdeclTorDecl = rdeclTorDecl
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
end (* functor ThmRecon *)
