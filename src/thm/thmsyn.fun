(* Theorems *)
(* Author: Carsten Schuermann *)

functor ThmSyn (structure ModeSyn' : MODESYN
		structure Abstract : ABSTRACT
		sharing Abstract.IntSyn = ModeSyn'.IntSyn
		structure Whnf : WHNF
		sharing Whnf.IntSyn = ModeSyn'.IntSyn
		structure Paths' : PATHS)
  : THMSYN =
struct
  structure ModeSyn = ModeSyn'
  structure Paths = Paths'

  exception Error of string
  fun error (r, msg) = raise Error (Paths.wrap (r, msg))


  type Param = string option

  datatype Order =
    Varg of string list
  | Lex of Order list
  | Simul of Order list

  datatype Callpats =
    Callpats of (ModeSyn.IntSyn.cid * Param list) list 

  (* Termination declaration *)
  datatype TDecl = 
    TDecl of (Order * Callpats)

  (* Theorem declaration *)
  datatype ThDecl =
    ThDecl of ModeSyn.IntSyn.Dec ModeSyn.IntSyn.Ctx * ModeSyn.Mode ModeSyn.IntSyn.Ctx * int

  (* Proof declaration *)
  datatype PDecl = 
    PDecl of int * TDecl

  local

    structure I = ModeSyn.IntSyn
    structure M = ModeSyn

    (* theoremDecToConDec (name, T) = D' 
     
       Invariant:
       If   name is the name of a theorem 
       and  T is the declaration of a theorem 
       then D' is a constant type declaration of this theorem
    *)

    fun theoremDecToConDec ((name, ThDecl (G, MG, i)), r) = 
	let 
	  (* theoremToConDec' G V = V'

	     Invariant:
	     If   G = V1 .. Vn
	     and  G |- V : kind
	     then V' = {V1} .. {Vn} V 
	     and  . |-  V' : kind
	  *)

	  fun theoremToConDec' (I.Null, V) = V
	    | theoremToConDec' (I.Decl (G, D), V) =
		if Abstract.closedDec (G, (D, I.id))
		  then theoremToConDec' (G, Abstract.piDepend ((Whnf.normalizeDec (D, I.id), 
								I.Maybe), V))
		else error (r, "Free variables in theorem declaration")
	in
	  I.ConDec (name, i, theoremToConDec' (G, I.Uni (I.Type)), I.Kind)
	end
   

    (* theoremDecToModeSpine (name, T) = mS' 
     
       Invariant:
       If   name is the name of a theorem 
       and  T is the declaration of a theorem 
       then mS' is a mode spine reflecting the 
	 quantifier information for the theorem
    *)

    fun theoremDecToModeSpine ((name,  ThDecl (G, MG, i)), r) = 
      let 
	fun theoremToModeSpine' (I.Null, I.Null, mS) = mS
	  | theoremToModeSpine' (I.Decl (G, I.Dec (x, _)), I.Decl (MG, m), mS) =
	      theoremToModeSpine' (G, MG, M.Mapp (M.Marg (m, x), mS))
      in
        theoremToModeSpine' (G, MG, M.Mnil)
      end

  in
    val theoremDecToConDec = theoremDecToConDec
    val theoremDecToModeSpine = theoremDecToModeSpine 
  end (* local *)

end; (* functor ThmSyn *)
