(* Reconstruct Termination Information *)
(* Author: Carsten Schuermann *)

functor ThmRecon (structure Global : GLOBAL
		  structure ModeSyn : MODESYN
		  structure ThmSyn': THMSYN
		  sharing ThmSyn'.ModeSyn = ModeSyn
		  sharing ThmSyn'.ModeSyn = ModeSyn
		  structure Paths' : PATHS
		  structure TpRecon': TP_RECON
		  sharing TpRecon'.Paths = Paths' 
		  sharing TpRecon'.IntSyn = ModeSyn.IntSyn
		  structure Names : NAMES
		  sharing Names.IntSyn = ModeSyn.IntSyn)
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

    fun callpats L = 
        let 
	  fun callpats' nil = (nil, nil)
	    | callpats' ((name, P, r) :: L) =  
	      let 
		val (cps, rs) =  (callpats' L)
	      in
		case Names.nameLookup name
		  of NONE => error (r, "Type family " ^ name ^ " not defined")
		   | SOME cid => ((cid, P) :: cps, (r :: rs))
	      end
	  val (cps, rs) = callpats' L
	in
	  (ThmSyn.Callpats (cps), rs)
	end

    type tdecl = ThmSyn.TDecl * (Paths.region * Paths.region list) 
    fun tdecl ((O, r), (C, rs)) = (ThmSyn.TDecl (O, C), (r, rs))
    fun tdeclTotDecl T  = T

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

    type ctx = T.dec I.Ctx
    val null = I.Null
    val decl = I.Decl

    type theorem = (I.Dec I.Ctx * ModeSyn.Mode I.Ctx * int) 
                   -> ((I.Dec I.Ctx * ModeSyn.Mode I.Ctx * int) * Paths.region)
    type theoremdec = string * theorem

    (* implicit arguments, Type, Modevector *)


    (* abstract (G1, M, G2, k, mode) = (G', M', k')
     
       Invariant:  
       If   G1 |- M   (where the k-prefix of G1 are implicit parameters)
       and  G1 |- G2 ctx
       and  mode is a mode
       then G' = G1, G2 (where the k'-prefix of G' are implicit parameters)
       and  M' = M, mode ... mode   (|G2| times)
       
    *)
    fun abstract (G, M, I.Null, k, _) = (G, M, k)
      | abstract (G, M, I.Decl (g, d), k, mode) =
	let 
	  val (G', M', k') = abstract (G, M, g, k, mode)
	  val D = T.decToDec (G', d)
	in
	  (I.Decl (G', D), I.Decl (M', mode), k)
	end
   
    fun top r (G, M, k) = ((G, M, k), r)
    fun exists (g, (r, t)) (G, M, k) = 
        let 
	  val (t', r') = t (abstract (G, M, g, k, M.Minus))
	in
	  (t', P.join (r, r'))
	end
    fun forall (g, (r, t)) (G, M, k) = 
        let 
	  val (t', r') = t (abstract (G, M, g, k, M.Plus))
	in
	  (t', P.join (r, r'))
	end
    fun forallStar (g, (r, t)) (G, M, k) = 
        let
	  val (t', r') = t (abstract (G, M, g, I.ctxLength g, M.Plus))
	in
	  (t', P.join (r, r'))
	end

    fun dec (name, t) = (name, t)

    fun theoremToTheorem t = 
        let
	  val _ = Names.varReset ()
	  val (t', r') = t (I.Null, I.Null, 0)
	in
	  (L.ThDecl t', r')
	end

    fun theoremDecToTheoremDec (name, t) =
        let 
	  val (td', r') = theoremToTheorem t
	in
          ((name, td'), r')
	end

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
      
    type prove = prove
    val prove = prove

    type establish = establish
    val establish = establish

    type assert = assert
    val assert = assert

    val tdeclTotDecl = tdeclTotDecl
    val proveToProve = proveToProve
    val establishToEstablish = establishToEstablish
    val assertToAssert = assertToAssert
      
    type ctx = ctx
    val null = null
    val decl = decl
      
    type theorem = theorem
    val top = top
    val forallStar = forallStar
    val forall = forall
    val exists = exists
    val theoremToTheorem = theoremToTheorem 

    type theoremdec = theoremdec
    val dec = dec
    val theoremDecToTheoremDec = theoremDecToTheoremDec 
  end (* local *)
end (* functor ThmRecon *)
