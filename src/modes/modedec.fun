(* Modes: short and full mode declarations *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor ModeDec (structure ModeSyn' : MODESYN
		 structure Paths' : PATHS)
  : MODEDEC =
struct
  structure ModeSyn = ModeSyn'
  structure Paths = Paths'

  exception Error of string

  local 
    structure M = ModeSyn
    structure I = ModeSyn.IntSyn
    structure P = Paths
      
    datatype Arg = Implicit | Explicit

    (* Representation invariant:
     
       The modes of parameters are represented in the following mode list

       M ::= . | M, <Marg, Arg>

       G corresponds to a context. We say M is a mode list for U, if
       G |- U : V and M assigns modes to parameters in G
         (and similarly for all other syntactic categories)
    *)
      
    fun error (r, msg) = raise Error (P.wrap (r, msg))

    fun lookup a =
        case M.modeLookup a
	  of NONE => raise Error ("No mode declaration for " ^ I.conDecName (I.sgnLookup a))
	   | SOME sM => sM 

    (* checkname mS = ()
       
       Invariant:
       mS modeSpine, all modes are named.
       If mS contains two entries with the same name 
       then Error is raised
    *)
    fun checkName (M.Mnil) = ()
      | checkName (M.Mapp (M.Marg (_, SOME name), mS)) = 
        let 
	  fun checkName' (M.Mnil) = ()
	    | checkName' (M.Mapp (M.Marg (_, SOME name'), mS)) = 
	      if name = name' then 
		raise Error ("Variable name clash: " ^ name ^ " is not unique")
	      else checkName' mS
	in
	  checkName' mS
	end

    (* modeConsistent (m1, m2) = B

       Invariant:
       
       If   mode (x) = m1
       and  G (x) defined
       and  G |- V : L
       and  mode (V) = m2
       then B = true iff   m1 consistent with m2

       m1\m2 + * -

        +    Y Y Y
        *    N N Y
        -    N N Y
    *)
    fun modeConsistent (M.Plus, _) = true
      | modeConsistent (_, M.Minus) = true
      | modeConsistent _ = false

    (* empty (k, ms, V) = (ms', V') 
      
       Invariant: 
       If    V = {A_1} .. {A_n} V1   in Sigma
       and   V has k implicit arguments
       then  ms' = ms, <( *, NONE), Implicit>  ... <( *, NONE), Implicit>   (k times)
       and   V' = V1
    *)
    fun empty (0, ms, V) = (ms, V)
      | empty (k, ms, I.Pi (_, V)) =
          empty (k-1, I.Decl (ms, (M.Marg (M.Star, NONE), Implicit)), V)

    (* inferExp (ms, m, U) = ms'

       Invariant:
       If  ms is a mode list for U,   (U in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in U,
	 wrt. to m. (see inferVar)
    *)
    fun inferExp (ms, mode, I.Root (I.BVar (k), S)) =
          inferSpine (inferVar (ms, mode, k), mode, S)
      | inferExp (ms, mode, I.Root (I.Const (cid), S)) =
	  inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Root (I.Def (cid), S)) =
	  inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Root (I.FgnConst (cs, conDec), S)) =
	  inferSpine (ms, mode, S)
      | inferExp (ms, mode, I.Lam (D as I.Dec (nameOpt, _), U)) =
	  I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D), 
				      (M.Marg (mode, nameOpt), Explicit)), mode, U))
      | inferExp (ms, mode, I.Pi ((D as I.Dec (nameOpt, _), _), V)) =
	  I.ctxPop (inferExp (I.Decl (inferDec (ms, mode, D), 
				      (M.Marg (mode, nameOpt), Explicit)), mode, V)) (* cannot make any assumptions on what is inside a foreign object *)
      | inferExp (ms, mode, I.FgnExp _) = ms

    (* inferSpine (ms, m, S) = ms'

       Invariant:
       If  ms is a mode list for S,   (S in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in S,
	 wrt. to m. (see inferVar)
    *)
    and inferSpine (ms, mode, I.Nil) = ms
      | inferSpine (ms, mode, I.App (U, S)) = 
          inferSpine (inferExp (ms, mode, U), mode, S)
	  
    (* inferVar (ms, m, k) = ms'

       Invariant:
       If  ms is a mode list, 
       and k a variable pointing into ms    (call it mode mk)
       and m is a mode
       then ms' is the same as ms            (call the value of k in ms'  mk')   
       where mk' = m o mk
    
        m o mk  + * -
        -------------
	+       + + +
        *       + * -
	-       + - -   
    *)
    and inferVar (I.Decl (ms, (M.Marg (M.Star, nameOpt), Implicit)), mode, 1) = 
          I.Decl (ms, (M.Marg (mode, nameOpt), Implicit))
      | inferVar (I.Decl (ms, (M.Marg (_, nameOpt), Implicit)), M.Plus, 1) = 
          I.Decl (ms, (M.Marg (M.Plus, nameOpt), Implicit))
      | inferVar (ms as I.Decl (_, (_, Implicit)), _, 1) = 
	  ms
      | inferVar (ms as I.Decl (_, (M.Marg (mode', SOME name), Explicit)), mode, 1) =  
	if modeConsistent (mode', mode)
	  then ms 
	else raise Error ("Mode declaration for " ^ name ^ " expected to be "
			  ^ M.modeToString mode)
      | inferVar (I.Decl (ms, (marg as M.Marg (mode', _), arg)), mode, k) = 
	  I.Decl (inferVar (ms, mode, (k -1)), (marg, arg))

    (* inferDec (ms, m, x:V) = ms'

       Invariant:
       If  ms is a mode list for V,   (V in nf)
       and m is a mode
       then ms' is the mode list consistently updated for all parameters occurring in V,
	 wrt. to m.   (see inferVar)
    *)
    and inferDec (ms, mode, I.Dec (_, V)) = 
          inferExp (ms, mode, V)

    (* inferMode ((ms, V), mS) = ms'

       Invariant:
       If  ms is a mode list for V, 
       and mS is a mode spine,
       then ms' is the mode list for V which is consistent with V.
    *)
    fun inferMode ((ms, I.Uni(I.Type)), M.Mnil) = ms
      | inferMode ((_, I.Uni(I.Type)), _) = raise Error "Too many modes specified"
      | inferMode ((ms, I.Pi ((I.Dec (name, V1), _), V2)), M.Mapp (M.Marg (mode, _), mS)) =
          I.ctxPop (inferMode ((I.Decl (inferExp (ms, mode, V1), 
					(M.Marg (mode, name), Explicit)), V2), mS))
      | inferMode ((M, I.Root _), _) = 
          raise Error "Expected type family, found object constant"
      | inferMode _ = raise Error "Not enough modes specified"

    (* abstractMode (ms, mS) = mS'

       Invariant:
       If    V = {A1} .. {An} V1  is a type (with n implicit parameter)  
       and   ms is a mode list for V, 
       then  mS' = {m1} .. {mn} mS
       where m1 .. mn are the infered modes for the implicit parameters
    *)
    fun abstractMode (ms, mS) =
        let
	  fun abstractMode' (I.Null, mS, _) = mS
	    | abstractMode' (I.Decl (ms, (marg, _)), mS, k) = 
	        abstractMode' (ms, M.Mapp (marg, mS), k+1)
	in
	  abstractMode' (ms, mS, 1)
	end

    (* shortToFull (cid, mS, r) = mS'

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is a mode spine in short form (implicit parameters are not moded),
       then mS' is a mode spine in full form (all parameters are moded)

       Full form can be different then intended by the user.
    *)
    fun shortToFull (a, mS, r) =
      let 
	fun calcImplicit' (I.ConDec (_, _, k, _, V, _))  =
	      abstractMode (inferMode (empty (k, I.Null, V), mS), mS)
	    (* only possibility since type families cannot be defined *)
      in 
	(checkName mS; calcImplicit' (I.sgnLookup a)) 
	handle Error (msg) => error (r, msg)  (* re-raise Error with location *)
      end

    (* checkFull (a, mS, r) = ()

       Invariant:
       mS modeSpine, all modes are named.
       r is the text region of the mode declaration
       if mS is not a valid mode spine in full form then 
       exception Error is raised.
    *)
    fun checkFull (a, mS, r) =  
        (checkName mS; 
	 case I.sgnLookup a 
	   of I.ConDec (_, _, _, _, V, _)  =>
	       (inferMode ((I.Null, V), mS); ()))
              (* only possibility: no defined type families *)
	handle Error (msg) => error (r, msg)  (* re-raise error with location *)

  in
    val shortToFull = shortToFull
    val checkFull = checkFull
  end
end;  (* functor ModeDec *)
