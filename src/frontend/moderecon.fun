(* Reconstructing Mode Declarations *)
(* Author: Carsten Schuermann *)

functor ModeRecon (structure Global : GLOBAL
		   structure ModeSyn' : MODESYN
		   structure Pattern : PATTERN
		     sharing Pattern.IntSyn = ModeSyn'.IntSyn
		   structure Paths' : PATHS
		   structure ModePrint : MODEPRINT
		     sharing ModePrint.ModeSyn = ModeSyn'
		   structure ModeDec : MODEDEC
		     sharing ModeDec.ModeSyn = ModeSyn'
		     sharing ModeDec.Paths = Paths'
		   structure TpRecon' : TP_RECON
		     sharing TpRecon'.IntSyn = ModeSyn'.IntSyn)
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
      type mterm = I.dctx * M.Mode I.Ctx -> (I.cid * M.ModeSpine) * P.region

      fun mpi ((m, _), d, t) (G, D) =  
	  t (I.Decl (G, T.decToDec (G, d)), I.Decl (D, m))

      fun mroot (t, r) (G, D) = 
	  let
            (* convert term spine to mode spine *)
	    (* Each argument must be contractible to variable *)
	    fun convertSpine (I.Nil) = M.Mnil
	      | convertSpine (I.App (U, S)) = 
		let 
		  val k = Pattern.etaContract U
		          handle Pattern.Eta => 
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

	    val (a, mS) = convertExp (T.termToExp (G, t))
	  in
	    (ModeDec.checkFull (a, mS, r);  ((a, mS), r))
	  end

      fun toModedec t = t (I.Null, I.Null)

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
