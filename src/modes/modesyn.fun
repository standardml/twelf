(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning *)

functor ModeSyn (structure IntSyn' : INTSYN
		 structure Names : NAMES
		   sharing Names.IntSyn = IntSyn'
		 structure Table : TABLE where type key = int
		 structure Index : INDEX
		 sharing Index.IntSyn = IntSyn') : MODESYN =
struct
  structure IntSyn = IntSyn'

  exception Error of string

  datatype Mode = Plus | Star | Minus 
  datatype ModeSpine = Mnil | Mapp of Marg * ModeSpine
  and  Marg = Marg of Mode * IntSyn.name option
   
  local 
    structure I = IntSyn'
      
    val modeSignature : ModeSpine Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets mode array 
    *)

    fun reset () = Table.clear modeSignature
     
    (* installMode (a, mS) = ()
        
       Effect: the ModeSpine mS is stored with the type family a
    *)
    fun installMode (a, mS) =
        case Index.lookup a
	  of nil => Table.insert modeSignature (a, mS)
           | _ => raise Error ("Mode for predicate " ^ Names.constName a
			       ^ " declared after clauses defining it")

    (* modeLookup a = mS'

       Looks the mode of a in the mode array up.
    *)
    fun modeLookup a = Table.lookup modeSignature a
	

    (* modeEqual (M1, M2) = true iff M1 = M2 *)
    fun modeEqual (Plus, Plus) = true
      | modeEqual (Star, Star) = true
      | modeEqual (Minus, Minus) = true
      | modeEqual _ = false


    (* modeToString M = string
    
       converts a mode into a string for error messages
    *)
    fun modeToString Plus = "input (+)"
      | modeToString Star = "unrestricted (*)"
      | modeToString Minus = "output (-)"

  in
    val reset = reset
    val installMode = installMode
    val modeLookup = modeLookup
    val modeEqual = modeEqual
    val modeToString = modeToString
  end
end;  (* functor ModeSyn *)
