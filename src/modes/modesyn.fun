(* Mode Syntax *)
(* Author: Carsten Schuermann *)
(* Modified: Frank Pfenning, Roberto Virga *)

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
  and  Marg = Marg of Mode * string option
   
  local 
    structure I = IntSyn'
      
    val modeSignature : (ModeSpine list) Table.Table = Table.new(0);

    (* reset () = ()

       Effect: Resets mode array 
    *)

    fun reset () = Table.clear modeSignature
     
    (* modeLookup a = mSOpt

       Looks up the mode of a in the mode array (if they are multiple, returns the last one
       inserted.
    *)
    fun modeLookup a =
	  case (Table.lookup modeSignature a)
	    of SOME (mS :: _) => SOME(mS)
	     | NONE => NONE
	

    (* mmodeLookup a = mSs

       Looks up the modes of a in the mode array.
    *)
    fun mmodeLookup a =
	  case (Table.lookup modeSignature a)
	    of SOME mSs => mSs
	     | NONE => nil
	

    (* installMode (a, mS) = ()
        
       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               modes stored with a, they are replaced by mS
    *)
    fun installMode (a, mS) =
          Table.insert modeSignature (a, [mS])

    (* installMmode (a, mS) = ()
        
       Effect: the ModeSpine mS is stored with the type family a; if there were previous
               models stored with a, the new mode mS is added to them.
    *)
    fun installMmode (a, mS) =
          let
	    val mSs = mmodeLookup a
	  in
            Table.insert modeSignature (a, mS :: mSs)
	  end

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

    val installMmode = installMmode
    val mmodeLookup = mmodeLookup

    val modeEqual = modeEqual
    val modeToString = modeToString
  end
end;  (* functor ModeSyn *)
