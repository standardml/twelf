(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ModeRecon (structure Global : GLOBAL
		   structure ModeSyn' : MODESYN
		   structure Whnf : WHNF
		     sharing Whnf.IntSyn = ModeSyn'.IntSyn
		   structure Paths' : PATHS
                   structure Names : NAMES
                     sharing Names.IntSyn = ModeSyn'.IntSyn
		   structure ModePrint : MODEPRINT
		     sharing ModePrint.ModeSyn = ModeSyn'
		   structure ModeDec : MODEDEC
		     sharing ModeDec.ModeSyn = ModeSyn'
		     sharing ModeDec.Paths = Paths'
		   structure TpRecon' : TP_RECON
		     sharing TpRecon'.IntSyn = ModeSyn'.IntSyn
                     sharing TpRecon'.Paths = Paths')
  : MODE_RECON =
struct
  structure ModeSyn = ModeSyn'
  structure ExtSyn = TpRecon'
  structure Paths = Paths'

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))

  local
    structure M = ModeSyn
    structure I = ModeSyn.IntSyn
    structure T = ExtSyn
    structure P = Paths

    type mode = M.Mode * P.region

    fun plus r = (M.Plus, r)
    fun star r = (M.Star, r)
    fun minus r = (M.Minus, r)

    type modedec = (I.cid * M.ModeSpine) * P.region

    structure Short =
    struct
      type mterm = (I.cid * M.ModeSpine) * P.region
      type mspine = M.ModeSpine * P.region

      fun mnil r = (M.Mnil, r)
      fun mapp (((m, r1), name), (mS, r2)) = (M.Mapp (M.Marg (m, name), mS), P.join (r1, r2))
      fun mroot (id, r1, (mS, r2)) = 
          let val r = P.join (r1, r2)
	  in
	    case Names.nameLookup id
	      of NONE => error (r, "Undeclared identifier " ^ id ^ " cannot be moded")
	       | SOME a => ((a, ModeDec.shortToFull (a, mS, r)), r)
	  end

      fun toModedec nmS = nmS
    end  (* structure Short *)

    structure Full =
    struct
      type mterm2 = I.dctx * T.approxCtx * M.Mode I.Ctx -> (I.cid * M.ModeSpine) * P.region
      type mterm = T.approxCtx -> mterm2

      fun mpi2 (m, Da, t, r) (G, Ga, D) =
	  t (I.Decl (G, T.approxDecToDec (G, Ga, Da, r)), I.Decl (Ga, Da),
             I.Decl (D, m))

      fun mpi ((m, _), d, r, t) (Ga) =
          let
            val Da = T.decToApproxDec (Ga, d)
            val t' = t (I.Decl (Ga, Da))
          in
            mpi2 (m, Da, t', r)
          end

      fun mroot2 (Ua, r) (G, Ga, D) = 
	  let
            (* convert term spine to mode spine *)
	    (* Each argument must be contractible to variable *)
	    fun convertSpine (I.Nil) = M.Mnil
	      | convertSpine (I.App (U, S)) = 
		let 
		  val k = Whnf.etaContract U
		          handle Whnf.Eta => 
			    error (r, "Argument not a variable")  (* print U? -fp *)
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
	      | convertExp (I.Root (I.NSDef (d), S))  = 
		  (* error is signalled later in ModeDec.checkFull *)
		  (d, convertSpine S)
	      (* convertExp (I.Root (I.Skonst _, S)) can't occur *)
		  

	    val (a, mS) = convertExp (T.approxExpToExp (G, Ga, Ua))
	  in
	    (ModeDec.checkFull (a, mS, r);  ((a, mS), r))
	  end

      fun mroot (tm, r) (Ga) =
          let
            val Ua = T.termToApproxExp (Ga, tm)
          in
            mroot2 (Ua, r)
          end

      fun toModedec t =
          let
            val _ = Names.varReset ()
            val t' = t (I.Null)
            val t'' = t' (I.Null, I.Null, I.Null)
          in
            t''
          end

    end  (* structure Full *)

    fun modeToMode (m, r) = (m, r)

  in
    type mode = mode
    val plus = plus
    val star = star
    val minus = minus

    type modedec = modedec

    structure Short = Short
    structure Full = Full

    val modeToMode = modeToMode
  end   (* local ... *)
end;  (* functor ModeRecon *)
